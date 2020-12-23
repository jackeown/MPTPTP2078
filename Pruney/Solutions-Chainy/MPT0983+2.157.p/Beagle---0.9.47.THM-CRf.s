%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:24 EST 2020

% Result     : Theorem 5.21s
% Output     : CNFRefutation 5.21s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 536 expanded)
%              Number of leaves         :   45 ( 211 expanded)
%              Depth                    :   11
%              Number of atoms          :  269 (1707 expanded)
%              Number of equality atoms :   50 ( 185 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

tff(f_162,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_103,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_81,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_142,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_57,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_120,axiom,(
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

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_130,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_44,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_68,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22])).

tff(c_40,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_67,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34])).

tff(c_54,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1732,plain,(
    ! [D_316,C_317,A_318,B_319] :
      ( D_316 = C_317
      | ~ r2_relset_1(A_318,B_319,C_317,D_316)
      | ~ m1_subset_1(D_316,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319)))
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1738,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_1732])).

tff(c_1749,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1738])).

tff(c_2034,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1749])).

tff(c_2037,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2034])).

tff(c_2041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_2037])).

tff(c_2042,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1749])).

tff(c_970,plain,(
    ! [E_201,C_199,A_203,F_198,D_200,B_202] :
      ( m1_subset_1(k1_partfun1(A_203,B_202,C_199,D_200,E_201,F_198),k1_zfmisc_1(k2_zfmisc_1(A_203,D_200)))
      | ~ m1_subset_1(F_198,k1_zfmisc_1(k2_zfmisc_1(C_199,D_200)))
      | ~ v1_funct_1(F_198)
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202)))
      | ~ v1_funct_1(E_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_830,plain,(
    ! [D_170,C_171,A_172,B_173] :
      ( D_170 = C_171
      | ~ r2_relset_1(A_172,B_173,C_171,D_170)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_840,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_830])).

tff(c_859,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_840])).

tff(c_876,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_976,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_970,c_876])).

tff(c_1005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_976])).

tff(c_1006,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_1343,plain,(
    ! [A_278,B_280,C_281,D_282,E_279] :
      ( k1_xboole_0 = C_281
      | v2_funct_1(D_282)
      | ~ v2_funct_1(k1_partfun1(A_278,B_280,B_280,C_281,D_282,E_279))
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(B_280,C_281)))
      | ~ v1_funct_2(E_279,B_280,C_281)
      | ~ v1_funct_1(E_279)
      | ~ m1_subset_1(D_282,k1_zfmisc_1(k2_zfmisc_1(A_278,B_280)))
      | ~ v1_funct_2(D_282,A_278,B_280)
      | ~ v1_funct_1(D_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1345,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1006,c_1343])).

tff(c_1347,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_68,c_1345])).

tff(c_1348,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1347])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1381,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1379,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_1348,c_8])).

tff(c_209,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_223,plain,(
    ! [A_65] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_65,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_209])).

tff(c_232,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_1508,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_232])).

tff(c_1512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_1508])).

tff(c_1515,plain,(
    ! [A_298] : ~ r2_hidden(A_298,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_1520,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4,c_1515])).

tff(c_50,plain,(
    ! [E_44,D_42,A_39,C_41,B_40] :
      ( k1_xboole_0 = C_41
      | v2_funct_1(D_42)
      | ~ v2_funct_1(k1_partfun1(A_39,B_40,B_40,C_41,D_42,E_44))
      | ~ m1_subset_1(E_44,k1_zfmisc_1(k2_zfmisc_1(B_40,C_41)))
      | ~ v1_funct_2(E_44,B_40,C_41)
      | ~ v1_funct_1(E_44)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_42,A_39,B_40)
      | ~ v1_funct_1(D_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2026,plain,(
    ! [E_44,D_42,A_39,C_41,B_40] :
      ( C_41 = '#skF_5'
      | v2_funct_1(D_42)
      | ~ v2_funct_1(k1_partfun1(A_39,B_40,B_40,C_41,D_42,E_44))
      | ~ m1_subset_1(E_44,k1_zfmisc_1(k2_zfmisc_1(B_40,C_41)))
      | ~ v1_funct_2(E_44,B_40,C_41)
      | ~ v1_funct_1(E_44)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_42,A_39,B_40)
      | ~ v1_funct_1(D_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_50])).

tff(c_2049,plain,
    ( '#skF_5' = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2042,c_2026])).

tff(c_2056,plain,
    ( '#skF_5' = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_68,c_2049])).

tff(c_2057,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_2056])).

tff(c_1532,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_2])).

tff(c_2095,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_1532])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1529,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_5',B_4) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_1520,c_10])).

tff(c_2092,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2057,c_1529])).

tff(c_222,plain,(
    ! [A_65] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_65,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_209])).

tff(c_231,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_2259,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2092,c_231])).

tff(c_2263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2095,c_2259])).

tff(c_2266,plain,(
    ! [A_383] : ~ r2_hidden(A_383,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_2271,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_2266])).

tff(c_106,plain,(
    ! [A_52] : k6_relat_1(A_52) = k6_partfun1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_112,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_18])).

tff(c_125,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_68])).

tff(c_2296,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2271,c_125])).

tff(c_2304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_2296])).

tff(c_2305,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_16,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2324,plain,(
    ! [B_389,A_390] :
      ( v1_relat_1(B_389)
      | ~ m1_subset_1(B_389,k1_zfmisc_1(A_390))
      | ~ v1_relat_1(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2333,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_2324])).

tff(c_2342,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2333])).

tff(c_2381,plain,(
    ! [C_396,B_397,A_398] :
      ( v5_relat_1(C_396,B_397)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_398,B_397))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2399,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_2381])).

tff(c_2512,plain,(
    ! [A_419,B_420,D_421] :
      ( r2_relset_1(A_419,B_420,D_421,D_421)
      | ~ m1_subset_1(D_421,k1_zfmisc_1(k2_zfmisc_1(A_419,B_420))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2523,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_67,c_2512])).

tff(c_2526,plain,(
    ! [A_422,B_423,C_424] :
      ( k2_relset_1(A_422,B_423,C_424) = k2_relat_1(C_424)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(A_422,B_423))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2544,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2526])).

tff(c_2720,plain,(
    ! [E_460,F_457,C_458,B_461,D_459,A_462] :
      ( m1_subset_1(k1_partfun1(A_462,B_461,C_458,D_459,E_460,F_457),k1_zfmisc_1(k2_zfmisc_1(A_462,D_459)))
      | ~ m1_subset_1(F_457,k1_zfmisc_1(k2_zfmisc_1(C_458,D_459)))
      | ~ v1_funct_1(F_457)
      | ~ m1_subset_1(E_460,k1_zfmisc_1(k2_zfmisc_1(A_462,B_461)))
      | ~ v1_funct_1(E_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2580,plain,(
    ! [D_427,C_428,A_429,B_430] :
      ( D_427 = C_428
      | ~ r2_relset_1(A_429,B_430,C_428,D_427)
      | ~ m1_subset_1(D_427,k1_zfmisc_1(k2_zfmisc_1(A_429,B_430)))
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_429,B_430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2590,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_2580])).

tff(c_2609,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2590])).

tff(c_2626,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2609])).

tff(c_2726,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2720,c_2626])).

tff(c_2755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_2726])).

tff(c_2756,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2609])).

tff(c_3124,plain,(
    ! [A_559,B_560,C_561,D_562] :
      ( k2_relset_1(A_559,B_560,C_561) = B_560
      | ~ r2_relset_1(B_560,B_560,k1_partfun1(B_560,A_559,A_559,B_560,D_562,C_561),k6_partfun1(B_560))
      | ~ m1_subset_1(D_562,k1_zfmisc_1(k2_zfmisc_1(B_560,A_559)))
      | ~ v1_funct_2(D_562,B_560,A_559)
      | ~ v1_funct_1(D_562)
      | ~ m1_subset_1(C_561,k1_zfmisc_1(k2_zfmisc_1(A_559,B_560)))
      | ~ v1_funct_2(C_561,A_559,B_560)
      | ~ v1_funct_1(C_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3127,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2756,c_3124])).

tff(c_3132,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_2523,c_2544,c_3127])).

tff(c_36,plain,(
    ! [B_26] :
      ( v2_funct_2(B_26,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3138,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3132,c_36])).

tff(c_3142,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2342,c_2399,c_3132,c_3138])).

tff(c_3144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2305,c_3142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.21/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/1.97  
% 5.21/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/1.97  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.21/1.97  
% 5.21/1.97  %Foreground sorts:
% 5.21/1.97  
% 5.21/1.97  
% 5.21/1.97  %Background operators:
% 5.21/1.97  
% 5.21/1.97  
% 5.21/1.97  %Foreground operators:
% 5.21/1.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.21/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.21/1.97  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.21/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.21/1.97  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.21/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.21/1.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.21/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.21/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.21/1.97  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.21/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.21/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.21/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.21/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.21/1.97  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.21/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.21/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.21/1.97  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.21/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.21/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.21/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.21/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.21/1.97  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.21/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.21/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.21/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.21/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.21/1.97  
% 5.21/1.99  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.21/1.99  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.21/1.99  tff(f_103, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.21/1.99  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.21/1.99  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.21/1.99  tff(f_81, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.21/1.99  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.21/1.99  tff(f_142, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.21/1.99  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.21/1.99  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.21/1.99  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.21/1.99  tff(f_57, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 5.21/1.99  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.21/1.99  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.21/1.99  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.21/1.99  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.21/1.99  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.21/1.99  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.21/1.99  tff(c_52, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.21/1.99  tff(c_130, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 5.21/1.99  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.21/1.99  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.21/1.99  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.21/1.99  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.21/1.99  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.21/1.99  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.21/1.99  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.21/1.99  tff(c_44, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.21/1.99  tff(c_22, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.21/1.99  tff(c_68, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22])).
% 5.21/1.99  tff(c_40, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.21/1.99  tff(c_34, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.21/1.99  tff(c_67, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_34])).
% 5.21/1.99  tff(c_54, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.21/1.99  tff(c_1732, plain, (![D_316, C_317, A_318, B_319]: (D_316=C_317 | ~r2_relset_1(A_318, B_319, C_317, D_316) | ~m1_subset_1(D_316, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.21/1.99  tff(c_1738, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_1732])).
% 5.21/1.99  tff(c_1749, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1738])).
% 5.21/1.99  tff(c_2034, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1749])).
% 5.21/1.99  tff(c_2037, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_2034])).
% 5.21/1.99  tff(c_2041, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_2037])).
% 5.21/1.99  tff(c_2042, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1749])).
% 5.21/1.99  tff(c_970, plain, (![E_201, C_199, A_203, F_198, D_200, B_202]: (m1_subset_1(k1_partfun1(A_203, B_202, C_199, D_200, E_201, F_198), k1_zfmisc_1(k2_zfmisc_1(A_203, D_200))) | ~m1_subset_1(F_198, k1_zfmisc_1(k2_zfmisc_1(C_199, D_200))) | ~v1_funct_1(F_198) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))) | ~v1_funct_1(E_201))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.21/1.99  tff(c_830, plain, (![D_170, C_171, A_172, B_173]: (D_170=C_171 | ~r2_relset_1(A_172, B_173, C_171, D_170) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.21/1.99  tff(c_840, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_830])).
% 5.21/1.99  tff(c_859, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_840])).
% 5.21/1.99  tff(c_876, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_859])).
% 5.21/1.99  tff(c_976, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_970, c_876])).
% 5.21/1.99  tff(c_1005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_976])).
% 5.21/1.99  tff(c_1006, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_859])).
% 5.21/1.99  tff(c_1343, plain, (![A_278, B_280, C_281, D_282, E_279]: (k1_xboole_0=C_281 | v2_funct_1(D_282) | ~v2_funct_1(k1_partfun1(A_278, B_280, B_280, C_281, D_282, E_279)) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(B_280, C_281))) | ~v1_funct_2(E_279, B_280, C_281) | ~v1_funct_1(E_279) | ~m1_subset_1(D_282, k1_zfmisc_1(k2_zfmisc_1(A_278, B_280))) | ~v1_funct_2(D_282, A_278, B_280) | ~v1_funct_1(D_282))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.21/1.99  tff(c_1345, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1006, c_1343])).
% 5.21/1.99  tff(c_1347, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_68, c_1345])).
% 5.21/1.99  tff(c_1348, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_130, c_1347])).
% 5.21/1.99  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.21/1.99  tff(c_1381, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_2])).
% 5.21/1.99  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.21/1.99  tff(c_1379, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_1348, c_8])).
% 5.21/1.99  tff(c_209, plain, (![C_63, B_64, A_65]: (~v1_xboole_0(C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.21/1.99  tff(c_223, plain, (![A_65]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_209])).
% 5.21/1.99  tff(c_232, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_223])).
% 5.21/1.99  tff(c_1508, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_232])).
% 5.21/1.99  tff(c_1512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1381, c_1508])).
% 5.21/1.99  tff(c_1515, plain, (![A_298]: (~r2_hidden(A_298, '#skF_5'))), inference(splitRight, [status(thm)], [c_223])).
% 5.21/1.99  tff(c_1520, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4, c_1515])).
% 5.21/1.99  tff(c_50, plain, (![E_44, D_42, A_39, C_41, B_40]: (k1_xboole_0=C_41 | v2_funct_1(D_42) | ~v2_funct_1(k1_partfun1(A_39, B_40, B_40, C_41, D_42, E_44)) | ~m1_subset_1(E_44, k1_zfmisc_1(k2_zfmisc_1(B_40, C_41))) | ~v1_funct_2(E_44, B_40, C_41) | ~v1_funct_1(E_44) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_42, A_39, B_40) | ~v1_funct_1(D_42))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.21/1.99  tff(c_2026, plain, (![E_44, D_42, A_39, C_41, B_40]: (C_41='#skF_5' | v2_funct_1(D_42) | ~v2_funct_1(k1_partfun1(A_39, B_40, B_40, C_41, D_42, E_44)) | ~m1_subset_1(E_44, k1_zfmisc_1(k2_zfmisc_1(B_40, C_41))) | ~v1_funct_2(E_44, B_40, C_41) | ~v1_funct_1(E_44) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_42, A_39, B_40) | ~v1_funct_1(D_42))), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_50])).
% 5.21/1.99  tff(c_2049, plain, ('#skF_5'='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2042, c_2026])).
% 5.21/1.99  tff(c_2056, plain, ('#skF_5'='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_68, c_2049])).
% 5.21/1.99  tff(c_2057, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_130, c_2056])).
% 5.21/1.99  tff(c_1532, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_2])).
% 5.21/1.99  tff(c_2095, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_1532])).
% 5.21/1.99  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.21/1.99  tff(c_1529, plain, (![B_4]: (k2_zfmisc_1('#skF_5', B_4)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_1520, c_10])).
% 5.21/1.99  tff(c_2092, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_2057, c_1529])).
% 5.21/1.99  tff(c_222, plain, (![A_65]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_65, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_209])).
% 5.21/1.99  tff(c_231, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_222])).
% 5.21/1.99  tff(c_2259, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2092, c_231])).
% 5.21/1.99  tff(c_2263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2095, c_2259])).
% 5.21/1.99  tff(c_2266, plain, (![A_383]: (~r2_hidden(A_383, '#skF_4'))), inference(splitRight, [status(thm)], [c_222])).
% 5.21/1.99  tff(c_2271, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_2266])).
% 5.21/1.99  tff(c_106, plain, (![A_52]: (k6_relat_1(A_52)=k6_partfun1(A_52))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.21/1.99  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.21/1.99  tff(c_112, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_106, c_18])).
% 5.21/1.99  tff(c_125, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_112, c_68])).
% 5.21/1.99  tff(c_2296, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2271, c_125])).
% 5.21/1.99  tff(c_2304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_2296])).
% 5.21/1.99  tff(c_2305, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 5.21/1.99  tff(c_16, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.21/1.99  tff(c_2324, plain, (![B_389, A_390]: (v1_relat_1(B_389) | ~m1_subset_1(B_389, k1_zfmisc_1(A_390)) | ~v1_relat_1(A_390))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.21/1.99  tff(c_2333, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_2324])).
% 5.21/1.99  tff(c_2342, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2333])).
% 5.21/1.99  tff(c_2381, plain, (![C_396, B_397, A_398]: (v5_relat_1(C_396, B_397) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_398, B_397))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.21/1.99  tff(c_2399, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_2381])).
% 5.21/1.99  tff(c_2512, plain, (![A_419, B_420, D_421]: (r2_relset_1(A_419, B_420, D_421, D_421) | ~m1_subset_1(D_421, k1_zfmisc_1(k2_zfmisc_1(A_419, B_420))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.21/1.99  tff(c_2523, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_67, c_2512])).
% 5.21/1.99  tff(c_2526, plain, (![A_422, B_423, C_424]: (k2_relset_1(A_422, B_423, C_424)=k2_relat_1(C_424) | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(A_422, B_423))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.21/1.99  tff(c_2544, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_2526])).
% 5.21/1.99  tff(c_2720, plain, (![E_460, F_457, C_458, B_461, D_459, A_462]: (m1_subset_1(k1_partfun1(A_462, B_461, C_458, D_459, E_460, F_457), k1_zfmisc_1(k2_zfmisc_1(A_462, D_459))) | ~m1_subset_1(F_457, k1_zfmisc_1(k2_zfmisc_1(C_458, D_459))) | ~v1_funct_1(F_457) | ~m1_subset_1(E_460, k1_zfmisc_1(k2_zfmisc_1(A_462, B_461))) | ~v1_funct_1(E_460))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.21/1.99  tff(c_2580, plain, (![D_427, C_428, A_429, B_430]: (D_427=C_428 | ~r2_relset_1(A_429, B_430, C_428, D_427) | ~m1_subset_1(D_427, k1_zfmisc_1(k2_zfmisc_1(A_429, B_430))) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_429, B_430))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.21/1.99  tff(c_2590, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_2580])).
% 5.21/1.99  tff(c_2609, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2590])).
% 5.21/1.99  tff(c_2626, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2609])).
% 5.21/1.99  tff(c_2726, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2720, c_2626])).
% 5.21/1.99  tff(c_2755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_2726])).
% 5.21/1.99  tff(c_2756, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2609])).
% 5.21/1.99  tff(c_3124, plain, (![A_559, B_560, C_561, D_562]: (k2_relset_1(A_559, B_560, C_561)=B_560 | ~r2_relset_1(B_560, B_560, k1_partfun1(B_560, A_559, A_559, B_560, D_562, C_561), k6_partfun1(B_560)) | ~m1_subset_1(D_562, k1_zfmisc_1(k2_zfmisc_1(B_560, A_559))) | ~v1_funct_2(D_562, B_560, A_559) | ~v1_funct_1(D_562) | ~m1_subset_1(C_561, k1_zfmisc_1(k2_zfmisc_1(A_559, B_560))) | ~v1_funct_2(C_561, A_559, B_560) | ~v1_funct_1(C_561))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.21/1.99  tff(c_3127, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2756, c_3124])).
% 5.21/1.99  tff(c_3132, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_2523, c_2544, c_3127])).
% 5.21/1.99  tff(c_36, plain, (![B_26]: (v2_funct_2(B_26, k2_relat_1(B_26)) | ~v5_relat_1(B_26, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.21/1.99  tff(c_3138, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3132, c_36])).
% 5.21/1.99  tff(c_3142, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2342, c_2399, c_3132, c_3138])).
% 5.21/1.99  tff(c_3144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2305, c_3142])).
% 5.21/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/1.99  
% 5.21/1.99  Inference rules
% 5.21/1.99  ----------------------
% 5.21/1.99  #Ref     : 0
% 5.21/1.99  #Sup     : 677
% 5.21/1.99  #Fact    : 0
% 5.21/1.99  #Define  : 0
% 5.21/1.99  #Split   : 21
% 5.21/1.99  #Chain   : 0
% 5.21/1.99  #Close   : 0
% 5.21/1.99  
% 5.21/1.99  Ordering : KBO
% 5.21/1.99  
% 5.21/1.99  Simplification rules
% 5.21/1.99  ----------------------
% 5.21/1.99  #Subsume      : 59
% 5.21/1.99  #Demod        : 761
% 5.21/1.99  #Tautology    : 249
% 5.21/1.99  #SimpNegUnit  : 8
% 5.21/1.99  #BackRed      : 181
% 5.21/1.99  
% 5.21/1.99  #Partial instantiations: 0
% 5.21/1.99  #Strategies tried      : 1
% 5.21/1.99  
% 5.21/1.99  Timing (in seconds)
% 5.21/1.99  ----------------------
% 5.21/2.00  Preprocessing        : 0.36
% 5.21/2.00  Parsing              : 0.19
% 5.21/2.00  CNF conversion       : 0.03
% 5.21/2.00  Main loop            : 0.86
% 5.21/2.00  Inferencing          : 0.29
% 5.21/2.00  Reduction            : 0.32
% 5.21/2.00  Demodulation         : 0.22
% 5.21/2.00  BG Simplification    : 0.03
% 5.21/2.00  Subsumption          : 0.14
% 5.21/2.00  Abstraction          : 0.03
% 5.21/2.00  MUC search           : 0.00
% 5.21/2.00  Cooper               : 0.00
% 5.21/2.00  Total                : 1.26
% 5.21/2.00  Index Insertion      : 0.00
% 5.21/2.00  Index Deletion       : 0.00
% 5.21/2.00  Index Matching       : 0.00
% 5.21/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
