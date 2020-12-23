%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:15 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 397 expanded)
%              Number of leaves         :   46 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 (1273 expanded)
%              Number of equality atoms :   41 ( 141 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
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

tff(f_117,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_156,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_95,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_41,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_134,axiom,(
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

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_127,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_46,plain,(
    ! [A_55] : k6_relat_1(A_55) = k6_partfun1(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_16,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_1356,plain,(
    ! [A_315,F_314,E_312,C_311,D_316,B_313] :
      ( m1_subset_1(k1_partfun1(A_315,B_313,C_311,D_316,E_312,F_314),k1_zfmisc_1(k2_zfmisc_1(A_315,D_316)))
      | ~ m1_subset_1(F_314,k1_zfmisc_1(k2_zfmisc_1(C_311,D_316)))
      | ~ v1_funct_1(F_314)
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(A_315,B_313)))
      | ~ v1_funct_1(E_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_32,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_69,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_32])).

tff(c_56,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1135,plain,(
    ! [D_264,C_265,A_266,B_267] :
      ( D_264 = C_265
      | ~ r2_relset_1(A_266,B_267,C_265,D_264)
      | ~ m1_subset_1(D_264,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267)))
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1145,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_56,c_1135])).

tff(c_1164,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1145])).

tff(c_1213,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1164])).

tff(c_1366,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1356,c_1213])).

tff(c_1393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_1366])).

tff(c_1394,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1164])).

tff(c_2005,plain,(
    ! [E_447,B_450,C_448,A_451,D_449] :
      ( k1_xboole_0 = C_448
      | v2_funct_1(D_449)
      | ~ v2_funct_1(k1_partfun1(A_451,B_450,B_450,C_448,D_449,E_447))
      | ~ m1_subset_1(E_447,k1_zfmisc_1(k2_zfmisc_1(B_450,C_448)))
      | ~ v1_funct_2(E_447,B_450,C_448)
      | ~ v1_funct_1(E_447)
      | ~ m1_subset_1(D_449,k1_zfmisc_1(k2_zfmisc_1(A_451,B_450)))
      | ~ v1_funct_2(D_449,A_451,B_450)
      | ~ v1_funct_1(D_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2007,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_2005])).

tff(c_2009,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_60,c_58,c_70,c_2007])).

tff(c_2010,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_2009])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2062,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_2',B_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_2010,c_8])).

tff(c_2193,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2062,c_64])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1'(A_25),A_25)
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_246,plain,(
    ! [C_95,A_96,B_97] :
      ( r2_hidden(C_95,A_96)
      | ~ r2_hidden(C_95,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1417,plain,(
    ! [A_318,A_319] :
      ( r2_hidden('#skF_1'(A_318),A_319)
      | ~ m1_subset_1(A_318,k1_zfmisc_1(A_319))
      | k1_xboole_0 = A_318 ) ),
    inference(resolution,[status(thm)],[c_36,c_246])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1430,plain,(
    ! [A_320,A_321] :
      ( ~ r1_tarski(A_320,'#skF_1'(A_321))
      | ~ m1_subset_1(A_321,k1_zfmisc_1(A_320))
      | k1_xboole_0 = A_321 ) ),
    inference(resolution,[status(thm)],[c_1417,c_18])).

tff(c_1435,plain,(
    ! [A_321] :
      ( ~ m1_subset_1(A_321,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = A_321 ) ),
    inference(resolution,[status(thm)],[c_2,c_1430])).

tff(c_2513,plain,(
    ! [A_499] :
      ( ~ m1_subset_1(A_499,k1_zfmisc_1('#skF_2'))
      | A_499 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_2010,c_1435])).

tff(c_2524,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2193,c_2513])).

tff(c_103,plain,(
    ! [A_73] : k6_relat_1(A_73) = k6_partfun1(A_73) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_12])).

tff(c_122,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_70])).

tff(c_2058,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_122])).

tff(c_2600,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2524,c_2058])).

tff(c_2613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_2600])).

tff(c_2614,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2646,plain,(
    ! [C_510,A_511,B_512] :
      ( v1_relat_1(C_510)
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2662,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2646])).

tff(c_2681,plain,(
    ! [C_516,B_517,A_518] :
      ( v5_relat_1(C_516,B_517)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(A_518,B_517))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2698,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2681])).

tff(c_2783,plain,(
    ! [A_537,B_538,D_539] :
      ( r2_relset_1(A_537,B_538,D_539,D_539)
      | ~ m1_subset_1(D_539,k1_zfmisc_1(k2_zfmisc_1(A_537,B_538))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2794,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_69,c_2783])).

tff(c_2807,plain,(
    ! [A_541,B_542,C_543] :
      ( k2_relset_1(A_541,B_542,C_543) = k2_relat_1(C_543)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2824,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2807])).

tff(c_3073,plain,(
    ! [B_595,E_594,D_598,A_597,F_596,C_593] :
      ( m1_subset_1(k1_partfun1(A_597,B_595,C_593,D_598,E_594,F_596),k1_zfmisc_1(k2_zfmisc_1(A_597,D_598)))
      | ~ m1_subset_1(F_596,k1_zfmisc_1(k2_zfmisc_1(C_593,D_598)))
      | ~ v1_funct_1(F_596)
      | ~ m1_subset_1(E_594,k1_zfmisc_1(k2_zfmisc_1(A_597,B_595)))
      | ~ v1_funct_1(E_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2847,plain,(
    ! [D_545,C_546,A_547,B_548] :
      ( D_545 = C_546
      | ~ r2_relset_1(A_547,B_548,C_546,D_545)
      | ~ m1_subset_1(D_545,k1_zfmisc_1(k2_zfmisc_1(A_547,B_548)))
      | ~ m1_subset_1(C_546,k1_zfmisc_1(k2_zfmisc_1(A_547,B_548))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2857,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_56,c_2847])).

tff(c_2876,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2857])).

tff(c_2926,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2876])).

tff(c_3081,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3073,c_2926])).

tff(c_3109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_62,c_58,c_3081])).

tff(c_3110,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2876])).

tff(c_3509,plain,(
    ! [A_706,B_707,C_708,D_709] :
      ( k2_relset_1(A_706,B_707,C_708) = B_707
      | ~ r2_relset_1(B_707,B_707,k1_partfun1(B_707,A_706,A_706,B_707,D_709,C_708),k6_partfun1(B_707))
      | ~ m1_subset_1(D_709,k1_zfmisc_1(k2_zfmisc_1(B_707,A_706)))
      | ~ v1_funct_2(D_709,B_707,A_706)
      | ~ v1_funct_1(D_709)
      | ~ m1_subset_1(C_708,k1_zfmisc_1(k2_zfmisc_1(A_706,B_707)))
      | ~ v1_funct_2(C_708,A_706,B_707)
      | ~ v1_funct_1(C_708) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3512,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3110,c_3509])).

tff(c_3517,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_68,c_66,c_64,c_2794,c_2824,c_3512])).

tff(c_38,plain,(
    ! [B_48] :
      ( v2_funct_2(B_48,k2_relat_1(B_48))
      | ~ v5_relat_1(B_48,k2_relat_1(B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3523,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3517,c_38])).

tff(c_3527,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2662,c_2698,c_3517,c_3523])).

tff(c_3529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2614,c_3527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:04:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.02/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.02/2.19  
% 6.02/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.02/2.19  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.02/2.19  
% 6.02/2.19  %Foreground sorts:
% 6.02/2.19  
% 6.02/2.19  
% 6.02/2.19  %Background operators:
% 6.02/2.19  
% 6.02/2.19  
% 6.02/2.19  %Foreground operators:
% 6.02/2.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.02/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.02/2.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.02/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.02/2.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.02/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.02/2.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.02/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.02/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.02/2.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.02/2.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.02/2.19  tff('#skF_5', type, '#skF_5': $i).
% 6.02/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.02/2.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.02/2.19  tff('#skF_2', type, '#skF_2': $i).
% 6.02/2.19  tff('#skF_3', type, '#skF_3': $i).
% 6.02/2.19  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.02/2.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.02/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.02/2.19  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.02/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.02/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.02/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.02/2.19  tff('#skF_4', type, '#skF_4': $i).
% 6.02/2.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.02/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.02/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.02/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.02/2.19  
% 6.02/2.21  tff(f_176, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.02/2.21  tff(f_117, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.02/2.21  tff(f_45, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.02/2.21  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.02/2.21  tff(f_74, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 6.02/2.21  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.02/2.21  tff(f_156, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.02/2.21  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.02/2.21  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.02/2.21  tff(f_95, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 6.02/2.21  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.02/2.21  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.02/2.21  tff(f_41, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 6.02/2.21  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.02/2.21  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.02/2.21  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.02/2.21  tff(f_134, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.02/2.21  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.02/2.21  tff(c_54, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.02/2.21  tff(c_127, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 6.02/2.21  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.02/2.21  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.02/2.21  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.02/2.21  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.02/2.21  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.02/2.21  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.02/2.21  tff(c_46, plain, (![A_55]: (k6_relat_1(A_55)=k6_partfun1(A_55))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.02/2.21  tff(c_16, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.02/2.21  tff(c_70, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 6.02/2.21  tff(c_1356, plain, (![A_315, F_314, E_312, C_311, D_316, B_313]: (m1_subset_1(k1_partfun1(A_315, B_313, C_311, D_316, E_312, F_314), k1_zfmisc_1(k2_zfmisc_1(A_315, D_316))) | ~m1_subset_1(F_314, k1_zfmisc_1(k2_zfmisc_1(C_311, D_316))) | ~v1_funct_1(F_314) | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(A_315, B_313))) | ~v1_funct_1(E_312))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.02/2.21  tff(c_32, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.02/2.21  tff(c_69, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_32])).
% 6.02/2.21  tff(c_56, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.02/2.21  tff(c_1135, plain, (![D_264, C_265, A_266, B_267]: (D_264=C_265 | ~r2_relset_1(A_266, B_267, C_265, D_264) | ~m1_subset_1(D_264, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.02/2.21  tff(c_1145, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_56, c_1135])).
% 6.02/2.21  tff(c_1164, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1145])).
% 6.02/2.21  tff(c_1213, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1164])).
% 6.02/2.21  tff(c_1366, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1356, c_1213])).
% 6.02/2.21  tff(c_1393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_1366])).
% 6.02/2.21  tff(c_1394, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1164])).
% 6.02/2.21  tff(c_2005, plain, (![E_447, B_450, C_448, A_451, D_449]: (k1_xboole_0=C_448 | v2_funct_1(D_449) | ~v2_funct_1(k1_partfun1(A_451, B_450, B_450, C_448, D_449, E_447)) | ~m1_subset_1(E_447, k1_zfmisc_1(k2_zfmisc_1(B_450, C_448))) | ~v1_funct_2(E_447, B_450, C_448) | ~v1_funct_1(E_447) | ~m1_subset_1(D_449, k1_zfmisc_1(k2_zfmisc_1(A_451, B_450))) | ~v1_funct_2(D_449, A_451, B_450) | ~v1_funct_1(D_449))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.02/2.21  tff(c_2007, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1394, c_2005])).
% 6.02/2.21  tff(c_2009, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_60, c_58, c_70, c_2007])).
% 6.02/2.21  tff(c_2010, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_127, c_2009])).
% 6.02/2.21  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.02/2.21  tff(c_2062, plain, (![B_3]: (k2_zfmisc_1('#skF_2', B_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_2010, c_8])).
% 6.02/2.21  tff(c_2193, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2062, c_64])).
% 6.02/2.21  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.02/2.21  tff(c_36, plain, (![A_25]: (r2_hidden('#skF_1'(A_25), A_25) | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.02/2.21  tff(c_246, plain, (![C_95, A_96, B_97]: (r2_hidden(C_95, A_96) | ~r2_hidden(C_95, B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.02/2.21  tff(c_1417, plain, (![A_318, A_319]: (r2_hidden('#skF_1'(A_318), A_319) | ~m1_subset_1(A_318, k1_zfmisc_1(A_319)) | k1_xboole_0=A_318)), inference(resolution, [status(thm)], [c_36, c_246])).
% 6.02/2.21  tff(c_18, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.02/2.21  tff(c_1430, plain, (![A_320, A_321]: (~r1_tarski(A_320, '#skF_1'(A_321)) | ~m1_subset_1(A_321, k1_zfmisc_1(A_320)) | k1_xboole_0=A_321)), inference(resolution, [status(thm)], [c_1417, c_18])).
% 6.02/2.21  tff(c_1435, plain, (![A_321]: (~m1_subset_1(A_321, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=A_321)), inference(resolution, [status(thm)], [c_2, c_1430])).
% 6.02/2.21  tff(c_2513, plain, (![A_499]: (~m1_subset_1(A_499, k1_zfmisc_1('#skF_2')) | A_499='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_2010, c_1435])).
% 6.02/2.21  tff(c_2524, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_2193, c_2513])).
% 6.02/2.21  tff(c_103, plain, (![A_73]: (k6_relat_1(A_73)=k6_partfun1(A_73))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.02/2.21  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.02/2.21  tff(c_109, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_103, c_12])).
% 6.02/2.21  tff(c_122, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_70])).
% 6.02/2.21  tff(c_2058, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_122])).
% 6.02/2.21  tff(c_2600, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2524, c_2058])).
% 6.02/2.21  tff(c_2613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_2600])).
% 6.02/2.21  tff(c_2614, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 6.02/2.21  tff(c_2646, plain, (![C_510, A_511, B_512]: (v1_relat_1(C_510) | ~m1_subset_1(C_510, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.02/2.21  tff(c_2662, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2646])).
% 6.02/2.21  tff(c_2681, plain, (![C_516, B_517, A_518]: (v5_relat_1(C_516, B_517) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(A_518, B_517))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.02/2.21  tff(c_2698, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_2681])).
% 6.02/2.21  tff(c_2783, plain, (![A_537, B_538, D_539]: (r2_relset_1(A_537, B_538, D_539, D_539) | ~m1_subset_1(D_539, k1_zfmisc_1(k2_zfmisc_1(A_537, B_538))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.02/2.21  tff(c_2794, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_69, c_2783])).
% 6.02/2.21  tff(c_2807, plain, (![A_541, B_542, C_543]: (k2_relset_1(A_541, B_542, C_543)=k2_relat_1(C_543) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.02/2.21  tff(c_2824, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2807])).
% 6.02/2.21  tff(c_3073, plain, (![B_595, E_594, D_598, A_597, F_596, C_593]: (m1_subset_1(k1_partfun1(A_597, B_595, C_593, D_598, E_594, F_596), k1_zfmisc_1(k2_zfmisc_1(A_597, D_598))) | ~m1_subset_1(F_596, k1_zfmisc_1(k2_zfmisc_1(C_593, D_598))) | ~v1_funct_1(F_596) | ~m1_subset_1(E_594, k1_zfmisc_1(k2_zfmisc_1(A_597, B_595))) | ~v1_funct_1(E_594))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.02/2.21  tff(c_2847, plain, (![D_545, C_546, A_547, B_548]: (D_545=C_546 | ~r2_relset_1(A_547, B_548, C_546, D_545) | ~m1_subset_1(D_545, k1_zfmisc_1(k2_zfmisc_1(A_547, B_548))) | ~m1_subset_1(C_546, k1_zfmisc_1(k2_zfmisc_1(A_547, B_548))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.02/2.21  tff(c_2857, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_56, c_2847])).
% 6.02/2.21  tff(c_2876, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2857])).
% 6.02/2.21  tff(c_2926, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2876])).
% 6.02/2.21  tff(c_3081, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_3073, c_2926])).
% 6.02/2.21  tff(c_3109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_62, c_58, c_3081])).
% 6.02/2.21  tff(c_3110, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2876])).
% 6.02/2.21  tff(c_3509, plain, (![A_706, B_707, C_708, D_709]: (k2_relset_1(A_706, B_707, C_708)=B_707 | ~r2_relset_1(B_707, B_707, k1_partfun1(B_707, A_706, A_706, B_707, D_709, C_708), k6_partfun1(B_707)) | ~m1_subset_1(D_709, k1_zfmisc_1(k2_zfmisc_1(B_707, A_706))) | ~v1_funct_2(D_709, B_707, A_706) | ~v1_funct_1(D_709) | ~m1_subset_1(C_708, k1_zfmisc_1(k2_zfmisc_1(A_706, B_707))) | ~v1_funct_2(C_708, A_706, B_707) | ~v1_funct_1(C_708))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.02/2.21  tff(c_3512, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3110, c_3509])).
% 6.02/2.21  tff(c_3517, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_68, c_66, c_64, c_2794, c_2824, c_3512])).
% 6.02/2.21  tff(c_38, plain, (![B_48]: (v2_funct_2(B_48, k2_relat_1(B_48)) | ~v5_relat_1(B_48, k2_relat_1(B_48)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.02/2.21  tff(c_3523, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3517, c_38])).
% 6.02/2.21  tff(c_3527, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2662, c_2698, c_3517, c_3523])).
% 6.02/2.21  tff(c_3529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2614, c_3527])).
% 6.02/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.02/2.21  
% 6.02/2.21  Inference rules
% 6.02/2.21  ----------------------
% 6.02/2.21  #Ref     : 0
% 6.02/2.21  #Sup     : 751
% 6.02/2.21  #Fact    : 0
% 6.02/2.21  #Define  : 0
% 6.02/2.21  #Split   : 11
% 6.02/2.21  #Chain   : 0
% 6.02/2.21  #Close   : 0
% 6.02/2.21  
% 6.02/2.21  Ordering : KBO
% 6.02/2.21  
% 6.02/2.21  Simplification rules
% 6.02/2.21  ----------------------
% 6.02/2.21  #Subsume      : 93
% 6.02/2.21  #Demod        : 811
% 6.02/2.21  #Tautology    : 222
% 6.02/2.21  #SimpNegUnit  : 8
% 6.02/2.21  #BackRed      : 236
% 6.02/2.21  
% 6.02/2.21  #Partial instantiations: 0
% 6.02/2.21  #Strategies tried      : 1
% 6.02/2.21  
% 6.02/2.21  Timing (in seconds)
% 6.02/2.21  ----------------------
% 6.02/2.22  Preprocessing        : 0.37
% 6.02/2.22  Parsing              : 0.19
% 6.02/2.22  CNF conversion       : 0.03
% 6.02/2.22  Main loop            : 1.07
% 6.02/2.22  Inferencing          : 0.38
% 6.02/2.22  Reduction            : 0.37
% 6.02/2.22  Demodulation         : 0.26
% 6.02/2.22  BG Simplification    : 0.04
% 6.02/2.22  Subsumption          : 0.20
% 6.02/2.22  Abstraction          : 0.04
% 6.02/2.22  MUC search           : 0.00
% 6.02/2.22  Cooper               : 0.00
% 6.02/2.22  Total                : 1.48
% 6.02/2.22  Index Insertion      : 0.00
% 6.02/2.22  Index Deletion       : 0.00
% 6.02/2.22  Index Matching       : 0.00
% 6.02/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
