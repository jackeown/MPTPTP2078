%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:30 EST 2020

% Result     : Theorem 5.83s
% Output     : CNFRefutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 372 expanded)
%              Number of leaves         :   44 ( 147 expanded)
%              Depth                    :   10
%              Number of atoms          :  199 (1188 expanded)
%              Number of equality atoms :   45 ( 340 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_135,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_71,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_123,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_60,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_20,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_210,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_225,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_210])).

tff(c_238,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_225])).

tff(c_269,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_292,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_269])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_24,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_77,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_24])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1309,plain,(
    ! [B_212,C_211,A_214,D_216,F_213,E_215] :
      ( m1_subset_1(k1_partfun1(A_214,B_212,C_211,D_216,E_215,F_213),k1_zfmisc_1(k2_zfmisc_1(A_214,D_216)))
      | ~ m1_subset_1(F_213,k1_zfmisc_1(k2_zfmisc_1(C_211,D_216)))
      | ~ v1_funct_1(F_213)
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_214,B_212)))
      | ~ v1_funct_1(E_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_54,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_745,plain,(
    ! [D_137,C_138,A_139,B_140] :
      ( D_137 = C_138
      | ~ r2_relset_1(A_139,B_140,C_138,D_137)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_761,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_745])).

tff(c_790,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_761])).

tff(c_902,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_790])).

tff(c_1322,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1309,c_902])).

tff(c_1359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_68,c_64,c_1322])).

tff(c_1360,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_790])).

tff(c_1575,plain,(
    ! [D_245,B_243,C_247,F_244,A_242,E_246] :
      ( k1_partfun1(A_242,B_243,C_247,D_245,E_246,F_244) = k5_relat_1(E_246,F_244)
      | ~ m1_subset_1(F_244,k1_zfmisc_1(k2_zfmisc_1(C_247,D_245)))
      | ~ v1_funct_1(F_244)
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ v1_funct_1(E_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1582,plain,(
    ! [A_242,B_243,E_246] :
      ( k1_partfun1(A_242,B_243,'#skF_2','#skF_1',E_246,'#skF_4') = k5_relat_1(E_246,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ v1_funct_1(E_246) ) ),
    inference(resolution,[status(thm)],[c_64,c_1575])).

tff(c_2224,plain,(
    ! [A_287,B_288,E_289] :
      ( k1_partfun1(A_287,B_288,'#skF_2','#skF_1',E_289,'#skF_4') = k5_relat_1(E_289,'#skF_4')
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_1(E_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1582])).

tff(c_2246,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2224])).

tff(c_2267,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1360,c_2246])).

tff(c_222,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_210])).

tff(c_235,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_222])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_415,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_437,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_415])).

tff(c_586,plain,(
    ! [B_111,A_112,C_113] :
      ( k1_xboole_0 = B_111
      | k1_relset_1(A_112,B_111,C_113) = A_112
      | ~ v1_funct_2(C_113,A_112,B_111)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_596,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_586])).

tff(c_611,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_437,c_596])).

tff(c_622,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_611])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_846,plain,(
    ! [B_149,A_150] :
      ( v2_funct_1(B_149)
      | ~ r1_tarski(k2_relat_1(B_149),k1_relat_1(A_150))
      | ~ v2_funct_1(k5_relat_1(B_149,A_150))
      | ~ v1_funct_1(B_149)
      | ~ v1_relat_1(B_149)
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2387,plain,(
    ! [B_290,A_291] :
      ( v2_funct_1(B_290)
      | ~ v2_funct_1(k5_relat_1(B_290,A_291))
      | ~ v1_funct_1(B_290)
      | ~ v1_funct_1(A_291)
      | ~ v1_relat_1(A_291)
      | ~ v5_relat_1(B_290,k1_relat_1(A_291))
      | ~ v1_relat_1(B_290) ) ),
    inference(resolution,[status(thm)],[c_18,c_846])).

tff(c_2402,plain,(
    ! [B_290] :
      ( v2_funct_1(B_290)
      | ~ v2_funct_1(k5_relat_1(B_290,'#skF_4'))
      | ~ v1_funct_1(B_290)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1(B_290,'#skF_2')
      | ~ v1_relat_1(B_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_2387])).

tff(c_2779,plain,(
    ! [B_311] :
      ( v2_funct_1(B_311)
      | ~ v2_funct_1(k5_relat_1(B_311,'#skF_4'))
      | ~ v1_funct_1(B_311)
      | ~ v5_relat_1(B_311,'#skF_2')
      | ~ v1_relat_1(B_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_68,c_2402])).

tff(c_2782,plain,
    ( v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2267,c_2779])).

tff(c_2784,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_292,c_76,c_77,c_2782])).

tff(c_2786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2784])).

tff(c_2787,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2809,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2787,c_2787,c_6])).

tff(c_132,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_132])).

tff(c_3120,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_147])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3223,plain,(
    ! [A_330] :
      ( A_330 = '#skF_1'
      | ~ r1_tarski(A_330,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2787,c_2787,c_2])).

tff(c_3238,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3120,c_3223])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2811,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2787,c_2787,c_8])).

tff(c_148,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_132])).

tff(c_3055,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2811,c_148])).

tff(c_3239,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3055,c_3223])).

tff(c_3281,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3238,c_3239])).

tff(c_3285,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3281,c_60])).

tff(c_122,plain,(
    ! [A_53] : m1_subset_1(k6_partfun1(A_53),k1_zfmisc_1(k2_zfmisc_1(A_53,A_53))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_126,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_122])).

tff(c_145,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_126,c_132])).

tff(c_152,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_163,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_77])).

tff(c_2806,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2787,c_163])).

tff(c_3260,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3238,c_2806])).

tff(c_3293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3285,c_3260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:05:50 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.83/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.10  
% 5.94/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/2.10  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.94/2.10  
% 5.94/2.10  %Foreground sorts:
% 5.94/2.10  
% 5.94/2.10  
% 5.94/2.10  %Background operators:
% 5.94/2.10  
% 5.94/2.10  
% 5.94/2.10  %Foreground operators:
% 5.94/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.94/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.94/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.10  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.94/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.94/2.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.94/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.94/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.94/2.10  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.94/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.94/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.94/2.10  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.94/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.94/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.94/2.10  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.94/2.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.94/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.94/2.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.94/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.94/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.94/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.94/2.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.94/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.94/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.94/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.94/2.10  
% 6.04/2.12  tff(f_158, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 6.04/2.12  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.04/2.12  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.04/2.12  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.04/2.12  tff(f_135, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.04/2.12  tff(f_71, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 6.04/2.12  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.04/2.12  tff(f_123, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.04/2.12  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.04/2.12  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.04/2.12  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.04/2.12  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.04/2.12  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.04/2.12  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 6.04/2.12  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.04/2.12  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.04/2.12  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.04/2.12  tff(c_60, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.04/2.12  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.04/2.12  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.04/2.12  tff(c_210, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.04/2.12  tff(c_225, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_210])).
% 6.04/2.12  tff(c_238, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_225])).
% 6.04/2.12  tff(c_269, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.04/2.12  tff(c_292, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_269])).
% 6.04/2.12  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.04/2.12  tff(c_58, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.04/2.12  tff(c_24, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.04/2.12  tff(c_77, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_24])).
% 6.04/2.12  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.04/2.12  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.04/2.12  tff(c_1309, plain, (![B_212, C_211, A_214, D_216, F_213, E_215]: (m1_subset_1(k1_partfun1(A_214, B_212, C_211, D_216, E_215, F_213), k1_zfmisc_1(k2_zfmisc_1(A_214, D_216))) | ~m1_subset_1(F_213, k1_zfmisc_1(k2_zfmisc_1(C_211, D_216))) | ~v1_funct_1(F_213) | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_214, B_212))) | ~v1_funct_1(E_215))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.04/2.12  tff(c_54, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.04/2.12  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.04/2.12  tff(c_745, plain, (![D_137, C_138, A_139, B_140]: (D_137=C_138 | ~r2_relset_1(A_139, B_140, C_138, D_137) | ~m1_subset_1(D_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.04/2.12  tff(c_761, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_745])).
% 6.04/2.12  tff(c_790, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_761])).
% 6.04/2.12  tff(c_902, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_790])).
% 6.04/2.12  tff(c_1322, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1309, c_902])).
% 6.04/2.12  tff(c_1359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_68, c_64, c_1322])).
% 6.04/2.12  tff(c_1360, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_790])).
% 6.04/2.12  tff(c_1575, plain, (![D_245, B_243, C_247, F_244, A_242, E_246]: (k1_partfun1(A_242, B_243, C_247, D_245, E_246, F_244)=k5_relat_1(E_246, F_244) | ~m1_subset_1(F_244, k1_zfmisc_1(k2_zfmisc_1(C_247, D_245))) | ~v1_funct_1(F_244) | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~v1_funct_1(E_246))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.04/2.12  tff(c_1582, plain, (![A_242, B_243, E_246]: (k1_partfun1(A_242, B_243, '#skF_2', '#skF_1', E_246, '#skF_4')=k5_relat_1(E_246, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~v1_funct_1(E_246))), inference(resolution, [status(thm)], [c_64, c_1575])).
% 6.04/2.12  tff(c_2224, plain, (![A_287, B_288, E_289]: (k1_partfun1(A_287, B_288, '#skF_2', '#skF_1', E_289, '#skF_4')=k5_relat_1(E_289, '#skF_4') | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_1(E_289))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1582])).
% 6.04/2.12  tff(c_2246, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2224])).
% 6.04/2.12  tff(c_2267, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1360, c_2246])).
% 6.04/2.12  tff(c_222, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_210])).
% 6.04/2.12  tff(c_235, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_222])).
% 6.04/2.12  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.04/2.12  tff(c_415, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.04/2.12  tff(c_437, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_415])).
% 6.04/2.12  tff(c_586, plain, (![B_111, A_112, C_113]: (k1_xboole_0=B_111 | k1_relset_1(A_112, B_111, C_113)=A_112 | ~v1_funct_2(C_113, A_112, B_111) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.04/2.12  tff(c_596, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_586])).
% 6.04/2.12  tff(c_611, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_437, c_596])).
% 6.04/2.12  tff(c_622, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_611])).
% 6.04/2.12  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.04/2.12  tff(c_846, plain, (![B_149, A_150]: (v2_funct_1(B_149) | ~r1_tarski(k2_relat_1(B_149), k1_relat_1(A_150)) | ~v2_funct_1(k5_relat_1(B_149, A_150)) | ~v1_funct_1(B_149) | ~v1_relat_1(B_149) | ~v1_funct_1(A_150) | ~v1_relat_1(A_150))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.04/2.12  tff(c_2387, plain, (![B_290, A_291]: (v2_funct_1(B_290) | ~v2_funct_1(k5_relat_1(B_290, A_291)) | ~v1_funct_1(B_290) | ~v1_funct_1(A_291) | ~v1_relat_1(A_291) | ~v5_relat_1(B_290, k1_relat_1(A_291)) | ~v1_relat_1(B_290))), inference(resolution, [status(thm)], [c_18, c_846])).
% 6.04/2.12  tff(c_2402, plain, (![B_290]: (v2_funct_1(B_290) | ~v2_funct_1(k5_relat_1(B_290, '#skF_4')) | ~v1_funct_1(B_290) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v5_relat_1(B_290, '#skF_2') | ~v1_relat_1(B_290))), inference(superposition, [status(thm), theory('equality')], [c_622, c_2387])).
% 6.04/2.12  tff(c_2779, plain, (![B_311]: (v2_funct_1(B_311) | ~v2_funct_1(k5_relat_1(B_311, '#skF_4')) | ~v1_funct_1(B_311) | ~v5_relat_1(B_311, '#skF_2') | ~v1_relat_1(B_311))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_68, c_2402])).
% 6.04/2.12  tff(c_2782, plain, (v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2267, c_2779])).
% 6.04/2.12  tff(c_2784, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_292, c_76, c_77, c_2782])).
% 6.04/2.12  tff(c_2786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2784])).
% 6.04/2.12  tff(c_2787, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_611])).
% 6.04/2.12  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.04/2.12  tff(c_2809, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2787, c_2787, c_6])).
% 6.04/2.12  tff(c_132, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.04/2.12  tff(c_147, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_132])).
% 6.04/2.12  tff(c_3120, plain, (r1_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_147])).
% 6.04/2.12  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.04/2.12  tff(c_3223, plain, (![A_330]: (A_330='#skF_1' | ~r1_tarski(A_330, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2787, c_2787, c_2])).
% 6.04/2.12  tff(c_3238, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_3120, c_3223])).
% 6.04/2.12  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.04/2.12  tff(c_2811, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2787, c_2787, c_8])).
% 6.04/2.12  tff(c_148, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_132])).
% 6.04/2.12  tff(c_3055, plain, (r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2811, c_148])).
% 6.04/2.12  tff(c_3239, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_3055, c_3223])).
% 6.04/2.12  tff(c_3281, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3238, c_3239])).
% 6.04/2.12  tff(c_3285, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3281, c_60])).
% 6.04/2.12  tff(c_122, plain, (![A_53]: (m1_subset_1(k6_partfun1(A_53), k1_zfmisc_1(k2_zfmisc_1(A_53, A_53))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.04/2.12  tff(c_126, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_122])).
% 6.04/2.12  tff(c_145, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_126, c_132])).
% 6.04/2.12  tff(c_152, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_145, c_2])).
% 6.04/2.12  tff(c_163, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152, c_77])).
% 6.04/2.12  tff(c_2806, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2787, c_163])).
% 6.04/2.12  tff(c_3260, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3238, c_2806])).
% 6.04/2.12  tff(c_3293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3285, c_3260])).
% 6.04/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.04/2.12  
% 6.04/2.12  Inference rules
% 6.04/2.12  ----------------------
% 6.04/2.12  #Ref     : 0
% 6.04/2.12  #Sup     : 689
% 6.04/2.12  #Fact    : 0
% 6.04/2.12  #Define  : 0
% 6.04/2.12  #Split   : 13
% 6.04/2.12  #Chain   : 0
% 6.04/2.12  #Close   : 0
% 6.04/2.12  
% 6.04/2.12  Ordering : KBO
% 6.04/2.12  
% 6.04/2.12  Simplification rules
% 6.04/2.12  ----------------------
% 6.04/2.12  #Subsume      : 76
% 6.04/2.12  #Demod        : 661
% 6.04/2.12  #Tautology    : 305
% 6.04/2.12  #SimpNegUnit  : 43
% 6.04/2.12  #BackRed      : 86
% 6.04/2.12  
% 6.04/2.12  #Partial instantiations: 0
% 6.04/2.12  #Strategies tried      : 1
% 6.04/2.12  
% 6.04/2.12  Timing (in seconds)
% 6.04/2.12  ----------------------
% 6.04/2.13  Preprocessing        : 0.37
% 6.04/2.13  Parsing              : 0.20
% 6.04/2.13  CNF conversion       : 0.03
% 6.04/2.13  Main loop            : 0.97
% 6.04/2.13  Inferencing          : 0.33
% 6.04/2.13  Reduction            : 0.35
% 6.04/2.13  Demodulation         : 0.26
% 6.04/2.13  BG Simplification    : 0.04
% 6.04/2.13  Subsumption          : 0.17
% 6.04/2.13  Abstraction          : 0.04
% 6.04/2.13  MUC search           : 0.00
% 6.04/2.13  Cooper               : 0.00
% 6.04/2.13  Total                : 1.38
% 6.04/2.13  Index Insertion      : 0.00
% 6.04/2.13  Index Deletion       : 0.00
% 6.04/2.13  Index Matching       : 0.00
% 6.04/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
