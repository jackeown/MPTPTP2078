%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:13 EST 2020

% Result     : Theorem 5.41s
% Output     : CNFRefutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 826 expanded)
%              Number of leaves         :   44 ( 295 expanded)
%              Depth                    :   12
%              Number of atoms          :  241 (2206 expanded)
%              Number of equality atoms :   53 ( 307 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_99,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_138,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
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

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_87,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_44,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    ! [A_11] : v2_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_557,plain,(
    ! [E_127,D_131,A_128,B_130,F_126,C_129] :
      ( m1_subset_1(k1_partfun1(A_128,B_130,C_129,D_131,E_127,F_126),k1_zfmisc_1(k2_zfmisc_1(A_128,D_131)))
      | ~ m1_subset_1(F_126,k1_zfmisc_1(k2_zfmisc_1(C_129,D_131)))
      | ~ v1_funct_1(F_126)
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_130)))
      | ~ v1_funct_1(E_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    ! [A_25] : m1_subset_1(k6_relat_1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_67,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34])).

tff(c_54,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_403,plain,(
    ! [D_98,C_99,A_100,B_101] :
      ( D_98 = C_99
      | ~ r2_relset_1(A_100,B_101,C_99,D_98)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_413,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_403])).

tff(c_432,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_413])).

tff(c_455,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_560,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_557,c_455])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_560])).

tff(c_592,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_1170,plain,(
    ! [A_269,C_271,D_270,B_272,E_268] :
      ( k1_xboole_0 = C_271
      | v2_funct_1(D_270)
      | ~ v2_funct_1(k1_partfun1(A_269,B_272,B_272,C_271,D_270,E_268))
      | ~ m1_subset_1(E_268,k1_zfmisc_1(k2_zfmisc_1(B_272,C_271)))
      | ~ v1_funct_2(E_268,B_272,C_271)
      | ~ v1_funct_1(E_268)
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(A_269,B_272)))
      | ~ v1_funct_2(D_270,A_269,B_272)
      | ~ v1_funct_1(D_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1172,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_1170])).

tff(c_1174,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_68,c_1172])).

tff(c_1175,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_1174])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1212,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_6])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1210,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_1175,c_12])).

tff(c_194,plain,(
    ! [C_71,B_72,A_73] :
      ( ~ v1_xboole_0(C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_208,plain,(
    ! [A_73] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_73,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_194])).

tff(c_279,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_1321,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_279])).

tff(c_1325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1212,c_1321])).

tff(c_1327,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_1328,plain,(
    ! [A_283] : ~ r2_hidden(A_283,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_1333,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_1328])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1337,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1333,c_8])).

tff(c_1469,plain,(
    ! [A_292] :
      ( A_292 = '#skF_5'
      | ~ v1_xboole_0(A_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_8])).

tff(c_1476,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1327,c_1469])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1855,plain,(
    ! [B_353,A_354] :
      ( B_353 = '#skF_5'
      | A_354 = '#skF_5'
      | k2_zfmisc_1(A_354,B_353) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_1337,c_1337,c_10])).

tff(c_1865,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1476,c_1855])).

tff(c_1881,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1865])).

tff(c_1902,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_1333])).

tff(c_1347,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_1337,c_12])).

tff(c_1897,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1881,c_1881,c_1347])).

tff(c_207,plain,(
    ! [A_73] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_73,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_194])).

tff(c_229,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_2022,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1897,c_229])).

tff(c_2026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1902,c_2022])).

tff(c_2027,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1865])).

tff(c_2050,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2027,c_1333])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1346,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_5',B_7) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_1337,c_14])).

tff(c_2044,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_2',B_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2027,c_2027,c_1346])).

tff(c_2127,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_229])).

tff(c_2131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2050,c_2127])).

tff(c_2134,plain,(
    ! [A_380] : ~ r2_hidden(A_380,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_2139,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_2134])).

tff(c_2144,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2139,c_8])).

tff(c_118,plain,(
    ! [A_56] : m1_subset_1(k6_partfun1(A_56),k1_zfmisc_1(k2_zfmisc_1(A_56,A_56))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34])).

tff(c_122,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_118])).

tff(c_196,plain,(
    ! [A_73] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_73,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_122,c_194])).

tff(c_205,plain,(
    ! [A_73] : ~ r2_hidden(A_73,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_196])).

tff(c_2160,plain,(
    ! [A_381] : ~ r2_hidden(A_381,k6_partfun1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2144,c_205])).

tff(c_2165,plain,(
    v1_xboole_0(k6_partfun1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_2160])).

tff(c_2206,plain,(
    ! [A_388] :
      ( A_388 = '#skF_4'
      | ~ v1_xboole_0(A_388) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2144,c_8])).

tff(c_2216,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2165,c_2206])).

tff(c_2235,plain,(
    v2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2216,c_68])).

tff(c_2242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_2235])).

tff(c_2243,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2285,plain,(
    ! [C_395,A_396,B_397] :
      ( v1_relat_1(C_395)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_396,B_397))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2301,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2285])).

tff(c_2320,plain,(
    ! [C_401,B_402,A_403] :
      ( v5_relat_1(C_401,B_402)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_403,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2337,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_2320])).

tff(c_2446,plain,(
    ! [A_419,B_420,D_421] :
      ( r2_relset_1(A_419,B_420,D_421,D_421)
      | ~ m1_subset_1(D_421,k1_zfmisc_1(k2_zfmisc_1(A_419,B_420))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2457,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_67,c_2446])).

tff(c_2505,plain,(
    ! [A_429,B_430,C_431] :
      ( k2_relset_1(A_429,B_430,C_431) = k2_relat_1(C_431)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_429,B_430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2522,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2505])).

tff(c_2706,plain,(
    ! [A_465,F_463,B_467,E_464,C_466,D_468] :
      ( m1_subset_1(k1_partfun1(A_465,B_467,C_466,D_468,E_464,F_463),k1_zfmisc_1(k2_zfmisc_1(A_465,D_468)))
      | ~ m1_subset_1(F_463,k1_zfmisc_1(k2_zfmisc_1(C_466,D_468)))
      | ~ v1_funct_1(F_463)
      | ~ m1_subset_1(E_464,k1_zfmisc_1(k2_zfmisc_1(A_465,B_467)))
      | ~ v1_funct_1(E_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2542,plain,(
    ! [D_433,C_434,A_435,B_436] :
      ( D_433 = C_434
      | ~ r2_relset_1(A_435,B_436,C_434,D_433)
      | ~ m1_subset_1(D_433,k1_zfmisc_1(k2_zfmisc_1(A_435,B_436)))
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_435,B_436))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2552,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_2542])).

tff(c_2571,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2552])).

tff(c_2600,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2571])).

tff(c_2709,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2706,c_2600])).

tff(c_2740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_2709])).

tff(c_2741,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2571])).

tff(c_3136,plain,(
    ! [A_588,B_589,C_590,D_591] :
      ( k2_relset_1(A_588,B_589,C_590) = B_589
      | ~ r2_relset_1(B_589,B_589,k1_partfun1(B_589,A_588,A_588,B_589,D_591,C_590),k6_partfun1(B_589))
      | ~ m1_subset_1(D_591,k1_zfmisc_1(k2_zfmisc_1(B_589,A_588)))
      | ~ v1_funct_2(D_591,B_589,A_588)
      | ~ v1_funct_1(D_591)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(A_588,B_589)))
      | ~ v1_funct_2(C_590,A_588,B_589)
      | ~ v1_funct_1(C_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3139,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2741,c_3136])).

tff(c_3144,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_2457,c_2522,c_3139])).

tff(c_36,plain,(
    ! [B_27] :
      ( v2_funct_2(B_27,k2_relat_1(B_27))
      | ~ v5_relat_1(B_27,k2_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3150,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3144,c_36])).

tff(c_3154,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_2337,c_3144,c_3150])).

tff(c_3156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2243,c_3154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:19:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.41/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.41/2.02  
% 5.41/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.41/2.03  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.41/2.03  
% 5.41/2.03  %Foreground sorts:
% 5.41/2.03  
% 5.41/2.03  
% 5.41/2.03  %Background operators:
% 5.41/2.03  
% 5.41/2.03  
% 5.41/2.03  %Foreground operators:
% 5.41/2.03  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.41/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.41/2.03  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.41/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.41/2.03  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.41/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.41/2.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.41/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.41/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.41/2.03  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.41/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.41/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.41/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.41/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.41/2.03  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.41/2.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.41/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.41/2.03  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.41/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.41/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.41/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.41/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.41/2.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.41/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.41/2.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.41/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.41/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.41/2.03  
% 5.41/2.05  tff(f_158, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.41/2.05  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.41/2.05  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.41/2.05  tff(f_53, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.41/2.05  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.41/2.05  tff(f_77, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.41/2.05  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.41/2.05  tff(f_138, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.41/2.05  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.41/2.05  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.41/2.05  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.41/2.05  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.41/2.05  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.41/2.05  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.41/2.05  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.41/2.05  tff(f_116, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.41/2.05  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.41/2.05  tff(c_52, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.05  tff(c_87, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 5.41/2.05  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.41/2.05  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.05  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.05  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.05  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.05  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.05  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.05  tff(c_44, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.41/2.05  tff(c_20, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.41/2.05  tff(c_68, plain, (![A_11]: (v2_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20])).
% 5.41/2.05  tff(c_557, plain, (![E_127, D_131, A_128, B_130, F_126, C_129]: (m1_subset_1(k1_partfun1(A_128, B_130, C_129, D_131, E_127, F_126), k1_zfmisc_1(k2_zfmisc_1(A_128, D_131))) | ~m1_subset_1(F_126, k1_zfmisc_1(k2_zfmisc_1(C_129, D_131))) | ~v1_funct_1(F_126) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_130))) | ~v1_funct_1(E_127))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.41/2.05  tff(c_34, plain, (![A_25]: (m1_subset_1(k6_relat_1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.41/2.05  tff(c_67, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_34])).
% 5.41/2.05  tff(c_54, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.41/2.05  tff(c_403, plain, (![D_98, C_99, A_100, B_101]: (D_98=C_99 | ~r2_relset_1(A_100, B_101, C_99, D_98) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.41/2.05  tff(c_413, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_403])).
% 5.41/2.05  tff(c_432, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_413])).
% 5.41/2.05  tff(c_455, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_432])).
% 5.41/2.05  tff(c_560, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_557, c_455])).
% 5.41/2.05  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_560])).
% 5.41/2.05  tff(c_592, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_432])).
% 5.41/2.05  tff(c_1170, plain, (![A_269, C_271, D_270, B_272, E_268]: (k1_xboole_0=C_271 | v2_funct_1(D_270) | ~v2_funct_1(k1_partfun1(A_269, B_272, B_272, C_271, D_270, E_268)) | ~m1_subset_1(E_268, k1_zfmisc_1(k2_zfmisc_1(B_272, C_271))) | ~v1_funct_2(E_268, B_272, C_271) | ~v1_funct_1(E_268) | ~m1_subset_1(D_270, k1_zfmisc_1(k2_zfmisc_1(A_269, B_272))) | ~v1_funct_2(D_270, A_269, B_272) | ~v1_funct_1(D_270))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.41/2.05  tff(c_1172, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_592, c_1170])).
% 5.41/2.05  tff(c_1174, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_68, c_1172])).
% 5.41/2.05  tff(c_1175, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_87, c_1174])).
% 5.41/2.05  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.41/2.05  tff(c_1212, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_6])).
% 5.41/2.05  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.41/2.05  tff(c_1210, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_1175, c_12])).
% 5.41/2.05  tff(c_194, plain, (![C_71, B_72, A_73]: (~v1_xboole_0(C_71) | ~m1_subset_1(B_72, k1_zfmisc_1(C_71)) | ~r2_hidden(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.41/2.05  tff(c_208, plain, (![A_73]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_73, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_194])).
% 5.41/2.05  tff(c_279, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_208])).
% 5.41/2.05  tff(c_1321, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1210, c_279])).
% 5.41/2.05  tff(c_1325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1212, c_1321])).
% 5.41/2.05  tff(c_1327, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_208])).
% 5.41/2.05  tff(c_1328, plain, (![A_283]: (~r2_hidden(A_283, '#skF_5'))), inference(splitRight, [status(thm)], [c_208])).
% 5.41/2.05  tff(c_1333, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_1328])).
% 5.41/2.05  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.41/2.05  tff(c_1337, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1333, c_8])).
% 5.41/2.05  tff(c_1469, plain, (![A_292]: (A_292='#skF_5' | ~v1_xboole_0(A_292))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_8])).
% 5.41/2.05  tff(c_1476, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(resolution, [status(thm)], [c_1327, c_1469])).
% 5.41/2.05  tff(c_10, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.41/2.05  tff(c_1855, plain, (![B_353, A_354]: (B_353='#skF_5' | A_354='#skF_5' | k2_zfmisc_1(A_354, B_353)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_1337, c_1337, c_10])).
% 5.41/2.05  tff(c_1865, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1476, c_1855])).
% 5.41/2.05  tff(c_1881, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_1865])).
% 5.41/2.05  tff(c_1902, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_1333])).
% 5.41/2.05  tff(c_1347, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_1337, c_12])).
% 5.41/2.05  tff(c_1897, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1881, c_1881, c_1347])).
% 5.41/2.05  tff(c_207, plain, (![A_73]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_73, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_194])).
% 5.41/2.05  tff(c_229, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_207])).
% 5.41/2.05  tff(c_2022, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1897, c_229])).
% 5.41/2.05  tff(c_2026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1902, c_2022])).
% 5.41/2.05  tff(c_2027, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_1865])).
% 5.41/2.05  tff(c_2050, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2027, c_1333])).
% 5.41/2.05  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.41/2.05  tff(c_1346, plain, (![B_7]: (k2_zfmisc_1('#skF_5', B_7)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_1337, c_14])).
% 5.41/2.05  tff(c_2044, plain, (![B_7]: (k2_zfmisc_1('#skF_2', B_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2027, c_2027, c_1346])).
% 5.41/2.05  tff(c_2127, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2044, c_229])).
% 5.41/2.05  tff(c_2131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2050, c_2127])).
% 5.41/2.05  tff(c_2134, plain, (![A_380]: (~r2_hidden(A_380, '#skF_4'))), inference(splitRight, [status(thm)], [c_207])).
% 5.41/2.05  tff(c_2139, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_2134])).
% 5.41/2.05  tff(c_2144, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2139, c_8])).
% 5.41/2.05  tff(c_118, plain, (![A_56]: (m1_subset_1(k6_partfun1(A_56), k1_zfmisc_1(k2_zfmisc_1(A_56, A_56))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_34])).
% 5.41/2.05  tff(c_122, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_118])).
% 5.41/2.05  tff(c_196, plain, (![A_73]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_73, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_122, c_194])).
% 5.41/2.05  tff(c_205, plain, (![A_73]: (~r2_hidden(A_73, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_196])).
% 5.41/2.05  tff(c_2160, plain, (![A_381]: (~r2_hidden(A_381, k6_partfun1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2144, c_205])).
% 5.41/2.05  tff(c_2165, plain, (v1_xboole_0(k6_partfun1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_2160])).
% 5.41/2.05  tff(c_2206, plain, (![A_388]: (A_388='#skF_4' | ~v1_xboole_0(A_388))), inference(demodulation, [status(thm), theory('equality')], [c_2144, c_8])).
% 5.41/2.05  tff(c_2216, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_2165, c_2206])).
% 5.41/2.05  tff(c_2235, plain, (v2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2216, c_68])).
% 5.41/2.05  tff(c_2242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_2235])).
% 5.41/2.05  tff(c_2243, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 5.41/2.05  tff(c_2285, plain, (![C_395, A_396, B_397]: (v1_relat_1(C_395) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_396, B_397))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.41/2.05  tff(c_2301, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2285])).
% 5.41/2.05  tff(c_2320, plain, (![C_401, B_402, A_403]: (v5_relat_1(C_401, B_402) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_403, B_402))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.41/2.05  tff(c_2337, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_2320])).
% 5.41/2.05  tff(c_2446, plain, (![A_419, B_420, D_421]: (r2_relset_1(A_419, B_420, D_421, D_421) | ~m1_subset_1(D_421, k1_zfmisc_1(k2_zfmisc_1(A_419, B_420))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.41/2.05  tff(c_2457, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_67, c_2446])).
% 5.41/2.05  tff(c_2505, plain, (![A_429, B_430, C_431]: (k2_relset_1(A_429, B_430, C_431)=k2_relat_1(C_431) | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_429, B_430))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.41/2.05  tff(c_2522, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2505])).
% 5.41/2.05  tff(c_2706, plain, (![A_465, F_463, B_467, E_464, C_466, D_468]: (m1_subset_1(k1_partfun1(A_465, B_467, C_466, D_468, E_464, F_463), k1_zfmisc_1(k2_zfmisc_1(A_465, D_468))) | ~m1_subset_1(F_463, k1_zfmisc_1(k2_zfmisc_1(C_466, D_468))) | ~v1_funct_1(F_463) | ~m1_subset_1(E_464, k1_zfmisc_1(k2_zfmisc_1(A_465, B_467))) | ~v1_funct_1(E_464))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.41/2.05  tff(c_2542, plain, (![D_433, C_434, A_435, B_436]: (D_433=C_434 | ~r2_relset_1(A_435, B_436, C_434, D_433) | ~m1_subset_1(D_433, k1_zfmisc_1(k2_zfmisc_1(A_435, B_436))) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_435, B_436))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.41/2.05  tff(c_2552, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_2542])).
% 5.41/2.05  tff(c_2571, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2552])).
% 5.41/2.05  tff(c_2600, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2571])).
% 5.41/2.05  tff(c_2709, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2706, c_2600])).
% 5.41/2.05  tff(c_2740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_2709])).
% 5.41/2.05  tff(c_2741, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2571])).
% 5.41/2.05  tff(c_3136, plain, (![A_588, B_589, C_590, D_591]: (k2_relset_1(A_588, B_589, C_590)=B_589 | ~r2_relset_1(B_589, B_589, k1_partfun1(B_589, A_588, A_588, B_589, D_591, C_590), k6_partfun1(B_589)) | ~m1_subset_1(D_591, k1_zfmisc_1(k2_zfmisc_1(B_589, A_588))) | ~v1_funct_2(D_591, B_589, A_588) | ~v1_funct_1(D_591) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(A_588, B_589))) | ~v1_funct_2(C_590, A_588, B_589) | ~v1_funct_1(C_590))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.41/2.05  tff(c_3139, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2741, c_3136])).
% 5.41/2.05  tff(c_3144, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_2457, c_2522, c_3139])).
% 5.41/2.05  tff(c_36, plain, (![B_27]: (v2_funct_2(B_27, k2_relat_1(B_27)) | ~v5_relat_1(B_27, k2_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.41/2.05  tff(c_3150, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3144, c_36])).
% 5.41/2.05  tff(c_3154, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2301, c_2337, c_3144, c_3150])).
% 5.41/2.05  tff(c_3156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2243, c_3154])).
% 5.41/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.41/2.05  
% 5.41/2.05  Inference rules
% 5.41/2.05  ----------------------
% 5.41/2.05  #Ref     : 0
% 5.41/2.05  #Sup     : 700
% 5.41/2.05  #Fact    : 0
% 5.41/2.05  #Define  : 0
% 5.41/2.05  #Split   : 17
% 5.41/2.05  #Chain   : 0
% 5.41/2.05  #Close   : 0
% 5.41/2.05  
% 5.41/2.05  Ordering : KBO
% 5.41/2.05  
% 5.41/2.05  Simplification rules
% 5.41/2.05  ----------------------
% 5.41/2.05  #Subsume      : 73
% 5.41/2.05  #Demod        : 703
% 5.41/2.05  #Tautology    : 236
% 5.41/2.05  #SimpNegUnit  : 5
% 5.41/2.05  #BackRed      : 175
% 5.41/2.05  
% 5.41/2.05  #Partial instantiations: 0
% 5.41/2.05  #Strategies tried      : 1
% 5.41/2.05  
% 5.41/2.05  Timing (in seconds)
% 5.41/2.05  ----------------------
% 5.41/2.05  Preprocessing        : 0.36
% 5.41/2.05  Parsing              : 0.19
% 5.41/2.05  CNF conversion       : 0.03
% 5.41/2.05  Main loop            : 0.91
% 5.41/2.05  Inferencing          : 0.32
% 5.41/2.05  Reduction            : 0.32
% 5.41/2.05  Demodulation         : 0.23
% 5.41/2.05  BG Simplification    : 0.04
% 5.41/2.05  Subsumption          : 0.16
% 5.41/2.05  Abstraction          : 0.04
% 5.41/2.05  MUC search           : 0.00
% 5.41/2.05  Cooper               : 0.00
% 5.41/2.05  Total                : 1.32
% 5.41/2.05  Index Insertion      : 0.00
% 5.41/2.05  Index Deletion       : 0.00
% 5.41/2.05  Index Matching       : 0.00
% 5.41/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
