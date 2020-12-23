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
% DateTime   : Thu Dec  3 10:12:15 EST 2020

% Result     : Theorem 6.12s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 337 expanded)
%              Number of leaves         :   46 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  187 (1121 expanded)
%              Number of equality atoms :   38 ( 116 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k3_mcart_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_171,negated_conjecture,(
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

tff(f_112,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_151,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_90,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_41,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_129,axiom,(
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

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_129,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_48,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_16,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_44,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,E_45] :
      ( m1_subset_1(k1_partfun1(A_41,B_42,C_43,D_44,E_45,F_46),k1_zfmisc_1(k2_zfmisc_1(A_41,D_44)))
      | ~ m1_subset_1(F_46,k1_zfmisc_1(k2_zfmisc_1(C_43,D_44)))
      | ~ v1_funct_1(F_46)
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(E_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_71,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_32])).

tff(c_58,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1153,plain,(
    ! [D_243,C_244,A_245,B_246] :
      ( D_243 = C_244
      | ~ r2_relset_1(A_245,B_246,C_244,D_243)
      | ~ m1_subset_1(D_243,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1165,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_58,c_1153])).

tff(c_1188,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1165])).

tff(c_2094,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1188])).

tff(c_2097,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2094])).

tff(c_2101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_2097])).

tff(c_2102,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1188])).

tff(c_2185,plain,(
    ! [D_396,B_397,E_393,A_395,C_394] :
      ( k1_xboole_0 = C_394
      | v2_funct_1(D_396)
      | ~ v2_funct_1(k1_partfun1(A_395,B_397,B_397,C_394,D_396,E_393))
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1(B_397,C_394)))
      | ~ v1_funct_2(E_393,B_397,C_394)
      | ~ v1_funct_1(E_393)
      | ~ m1_subset_1(D_396,k1_zfmisc_1(k2_zfmisc_1(A_395,B_397)))
      | ~ v1_funct_2(D_396,A_395,B_397)
      | ~ v1_funct_1(D_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2187,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2102,c_2185])).

tff(c_2189,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_72,c_2187])).

tff(c_2190,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_2189])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2236,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_2',B_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2190,c_2190,c_8])).

tff(c_2347,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_66])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1'(A_25),A_25)
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_248,plain,(
    ! [C_87,A_88,B_89] :
      ( r2_hidden(C_87,A_88)
      | ~ r2_hidden(C_87,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_282,plain,(
    ! [A_104,A_105] :
      ( r2_hidden('#skF_1'(A_104),A_105)
      | ~ m1_subset_1(A_104,k1_zfmisc_1(A_105))
      | k1_xboole_0 = A_104 ) ),
    inference(resolution,[status(thm)],[c_34,c_248])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1255,plain,(
    ! [A_260,A_261] :
      ( ~ r1_tarski(A_260,'#skF_1'(A_261))
      | ~ m1_subset_1(A_261,k1_zfmisc_1(A_260))
      | k1_xboole_0 = A_261 ) ),
    inference(resolution,[status(thm)],[c_282,c_18])).

tff(c_1260,plain,(
    ! [A_261] :
      ( ~ m1_subset_1(A_261,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = A_261 ) ),
    inference(resolution,[status(thm)],[c_2,c_1255])).

tff(c_2567,plain,(
    ! [A_434] :
      ( ~ m1_subset_1(A_434,k1_zfmisc_1('#skF_2'))
      | A_434 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2190,c_2190,c_1260])).

tff(c_2578,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2347,c_2567])).

tff(c_90,plain,(
    ! [A_64] : k6_relat_1(A_64) = k6_partfun1(A_64) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_96,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_12])).

tff(c_109,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_72])).

tff(c_2233,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2190,c_109])).

tff(c_2631,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2578,c_2233])).

tff(c_2643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_2631])).

tff(c_2644,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2687,plain,(
    ! [C_442,A_443,B_444] :
      ( v1_relat_1(C_442)
      | ~ m1_subset_1(C_442,k1_zfmisc_1(k2_zfmisc_1(A_443,B_444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2704,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_2687])).

tff(c_2728,plain,(
    ! [C_449,B_450,A_451] :
      ( v5_relat_1(C_449,B_450)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_451,B_450))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2746,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2728])).

tff(c_2876,plain,(
    ! [A_491,B_492,C_493] :
      ( k2_relset_1(A_491,B_492,C_493) = k2_relat_1(C_493)
      | ~ m1_subset_1(C_493,k1_zfmisc_1(k2_zfmisc_1(A_491,B_492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2894,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_2876])).

tff(c_3410,plain,(
    ! [A_574,B_575,C_576,D_577] :
      ( k2_relset_1(A_574,B_575,C_576) = B_575
      | ~ r2_relset_1(B_575,B_575,k1_partfun1(B_575,A_574,A_574,B_575,D_577,C_576),k6_partfun1(B_575))
      | ~ m1_subset_1(D_577,k1_zfmisc_1(k2_zfmisc_1(B_575,A_574)))
      | ~ v1_funct_2(D_577,B_575,A_574)
      | ~ v1_funct_1(D_577)
      | ~ m1_subset_1(C_576,k1_zfmisc_1(k2_zfmisc_1(A_574,B_575)))
      | ~ v1_funct_2(C_576,A_574,B_575)
      | ~ v1_funct_1(C_576) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3413,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_3410])).

tff(c_3419,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_2894,c_3413])).

tff(c_40,plain,(
    ! [B_40] :
      ( v2_funct_2(B_40,k2_relat_1(B_40))
      | ~ v5_relat_1(B_40,k2_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3425,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3419,c_40])).

tff(c_3429,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2704,c_2746,c_3419,c_3425])).

tff(c_3431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2644,c_3429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:25:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.12/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.23  
% 6.45/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.23  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k3_mcart_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.45/2.23  
% 6.45/2.23  %Foreground sorts:
% 6.45/2.23  
% 6.45/2.23  
% 6.45/2.23  %Background operators:
% 6.45/2.23  
% 6.45/2.23  
% 6.45/2.23  %Foreground operators:
% 6.45/2.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.45/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.45/2.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.45/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.45/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.45/2.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.45/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.45/2.23  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.45/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.45/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.45/2.23  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.45/2.23  tff('#skF_5', type, '#skF_5': $i).
% 6.45/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.45/2.23  tff('#skF_2', type, '#skF_2': $i).
% 6.45/2.23  tff('#skF_3', type, '#skF_3': $i).
% 6.45/2.23  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.45/2.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.45/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.45/2.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.45/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.45/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.45/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.45/2.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.45/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.45/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.45/2.23  
% 6.45/2.26  tff(f_171, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.45/2.26  tff(f_112, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.45/2.26  tff(f_45, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.45/2.26  tff(f_110, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.45/2.26  tff(f_74, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.45/2.26  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.45/2.26  tff(f_151, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.45/2.26  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.45/2.26  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.45/2.26  tff(f_90, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 6.45/2.26  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.45/2.26  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.45/2.26  tff(f_41, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.45/2.26  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.45/2.26  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.45/2.26  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.45/2.26  tff(f_129, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.45/2.26  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.45/2.26  tff(c_56, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.45/2.26  tff(c_129, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 6.45/2.26  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.45/2.26  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.45/2.26  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.45/2.26  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.45/2.26  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.45/2.26  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.45/2.26  tff(c_48, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.45/2.26  tff(c_16, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.45/2.26  tff(c_72, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 6.45/2.26  tff(c_44, plain, (![D_44, F_46, C_43, A_41, B_42, E_45]: (m1_subset_1(k1_partfun1(A_41, B_42, C_43, D_44, E_45, F_46), k1_zfmisc_1(k2_zfmisc_1(A_41, D_44))) | ~m1_subset_1(F_46, k1_zfmisc_1(k2_zfmisc_1(C_43, D_44))) | ~v1_funct_1(F_46) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(E_45))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.45/2.26  tff(c_32, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.45/2.26  tff(c_71, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_32])).
% 6.45/2.26  tff(c_58, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.45/2.26  tff(c_1153, plain, (![D_243, C_244, A_245, B_246]: (D_243=C_244 | ~r2_relset_1(A_245, B_246, C_244, D_243) | ~m1_subset_1(D_243, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.45/2.26  tff(c_1165, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_58, c_1153])).
% 6.45/2.26  tff(c_1188, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1165])).
% 6.45/2.26  tff(c_2094, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1188])).
% 6.45/2.26  tff(c_2097, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_2094])).
% 6.45/2.26  tff(c_2101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_2097])).
% 6.45/2.26  tff(c_2102, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1188])).
% 6.45/2.26  tff(c_2185, plain, (![D_396, B_397, E_393, A_395, C_394]: (k1_xboole_0=C_394 | v2_funct_1(D_396) | ~v2_funct_1(k1_partfun1(A_395, B_397, B_397, C_394, D_396, E_393)) | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1(B_397, C_394))) | ~v1_funct_2(E_393, B_397, C_394) | ~v1_funct_1(E_393) | ~m1_subset_1(D_396, k1_zfmisc_1(k2_zfmisc_1(A_395, B_397))) | ~v1_funct_2(D_396, A_395, B_397) | ~v1_funct_1(D_396))), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.45/2.26  tff(c_2187, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2102, c_2185])).
% 6.45/2.26  tff(c_2189, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_72, c_2187])).
% 6.45/2.26  tff(c_2190, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_129, c_2189])).
% 6.45/2.26  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.45/2.26  tff(c_2236, plain, (![B_3]: (k2_zfmisc_1('#skF_2', B_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2190, c_2190, c_8])).
% 6.45/2.26  tff(c_2347, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_66])).
% 6.45/2.26  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.45/2.26  tff(c_34, plain, (![A_25]: (r2_hidden('#skF_1'(A_25), A_25) | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.45/2.26  tff(c_248, plain, (![C_87, A_88, B_89]: (r2_hidden(C_87, A_88) | ~r2_hidden(C_87, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.45/2.26  tff(c_282, plain, (![A_104, A_105]: (r2_hidden('#skF_1'(A_104), A_105) | ~m1_subset_1(A_104, k1_zfmisc_1(A_105)) | k1_xboole_0=A_104)), inference(resolution, [status(thm)], [c_34, c_248])).
% 6.45/2.26  tff(c_18, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.45/2.26  tff(c_1255, plain, (![A_260, A_261]: (~r1_tarski(A_260, '#skF_1'(A_261)) | ~m1_subset_1(A_261, k1_zfmisc_1(A_260)) | k1_xboole_0=A_261)), inference(resolution, [status(thm)], [c_282, c_18])).
% 6.45/2.26  tff(c_1260, plain, (![A_261]: (~m1_subset_1(A_261, k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0=A_261)), inference(resolution, [status(thm)], [c_2, c_1255])).
% 6.45/2.26  tff(c_2567, plain, (![A_434]: (~m1_subset_1(A_434, k1_zfmisc_1('#skF_2')) | A_434='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2190, c_2190, c_1260])).
% 6.45/2.26  tff(c_2578, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_2347, c_2567])).
% 6.45/2.26  tff(c_90, plain, (![A_64]: (k6_relat_1(A_64)=k6_partfun1(A_64))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.45/2.26  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.45/2.26  tff(c_96, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_90, c_12])).
% 6.45/2.26  tff(c_109, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_72])).
% 6.45/2.26  tff(c_2233, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2190, c_109])).
% 6.45/2.26  tff(c_2631, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2578, c_2233])).
% 6.45/2.26  tff(c_2643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_2631])).
% 6.45/2.26  tff(c_2644, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 6.45/2.26  tff(c_2687, plain, (![C_442, A_443, B_444]: (v1_relat_1(C_442) | ~m1_subset_1(C_442, k1_zfmisc_1(k2_zfmisc_1(A_443, B_444))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.45/2.26  tff(c_2704, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_2687])).
% 6.45/2.26  tff(c_2728, plain, (![C_449, B_450, A_451]: (v5_relat_1(C_449, B_450) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_451, B_450))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.45/2.26  tff(c_2746, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_2728])).
% 6.45/2.26  tff(c_2876, plain, (![A_491, B_492, C_493]: (k2_relset_1(A_491, B_492, C_493)=k2_relat_1(C_493) | ~m1_subset_1(C_493, k1_zfmisc_1(k2_zfmisc_1(A_491, B_492))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.45/2.26  tff(c_2894, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_2876])).
% 6.45/2.26  tff(c_3410, plain, (![A_574, B_575, C_576, D_577]: (k2_relset_1(A_574, B_575, C_576)=B_575 | ~r2_relset_1(B_575, B_575, k1_partfun1(B_575, A_574, A_574, B_575, D_577, C_576), k6_partfun1(B_575)) | ~m1_subset_1(D_577, k1_zfmisc_1(k2_zfmisc_1(B_575, A_574))) | ~v1_funct_2(D_577, B_575, A_574) | ~v1_funct_1(D_577) | ~m1_subset_1(C_576, k1_zfmisc_1(k2_zfmisc_1(A_574, B_575))) | ~v1_funct_2(C_576, A_574, B_575) | ~v1_funct_1(C_576))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.45/2.26  tff(c_3413, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_3410])).
% 6.45/2.26  tff(c_3419, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_2894, c_3413])).
% 6.45/2.26  tff(c_40, plain, (![B_40]: (v2_funct_2(B_40, k2_relat_1(B_40)) | ~v5_relat_1(B_40, k2_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.45/2.26  tff(c_3425, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3419, c_40])).
% 6.45/2.26  tff(c_3429, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2704, c_2746, c_3419, c_3425])).
% 6.45/2.26  tff(c_3431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2644, c_3429])).
% 6.45/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.26  
% 6.45/2.26  Inference rules
% 6.45/2.26  ----------------------
% 6.45/2.26  #Ref     : 0
% 6.45/2.26  #Sup     : 700
% 6.45/2.26  #Fact    : 0
% 6.45/2.26  #Define  : 0
% 6.45/2.26  #Split   : 18
% 6.45/2.26  #Chain   : 0
% 6.45/2.26  #Close   : 0
% 6.45/2.26  
% 6.45/2.26  Ordering : KBO
% 6.45/2.26  
% 6.45/2.26  Simplification rules
% 6.45/2.26  ----------------------
% 6.45/2.26  #Subsume      : 82
% 6.45/2.26  #Demod        : 1075
% 6.45/2.26  #Tautology    : 196
% 6.45/2.26  #SimpNegUnit  : 10
% 6.45/2.26  #BackRed      : 457
% 6.45/2.26  
% 6.45/2.26  #Partial instantiations: 0
% 6.45/2.26  #Strategies tried      : 1
% 6.45/2.26  
% 6.45/2.26  Timing (in seconds)
% 6.45/2.26  ----------------------
% 6.45/2.26  Preprocessing        : 0.38
% 6.45/2.26  Parsing              : 0.20
% 6.45/2.26  CNF conversion       : 0.03
% 6.45/2.26  Main loop            : 1.09
% 6.45/2.26  Inferencing          : 0.36
% 6.45/2.26  Reduction            : 0.38
% 6.45/2.26  Demodulation         : 0.27
% 6.45/2.26  BG Simplification    : 0.04
% 6.45/2.26  Subsumption          : 0.21
% 6.45/2.26  Abstraction          : 0.04
% 6.45/2.26  MUC search           : 0.00
% 6.45/2.26  Cooper               : 0.00
% 6.45/2.26  Total                : 1.52
% 6.45/2.26  Index Insertion      : 0.00
% 6.45/2.26  Index Deletion       : 0.00
% 6.45/2.26  Index Matching       : 0.00
% 6.45/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
