%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:12 EST 2020

% Result     : Theorem 5.85s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 873 expanded)
%              Number of leaves         :   42 ( 324 expanded)
%              Depth                    :   10
%              Number of atoms          :  299 (2701 expanded)
%              Number of equality atoms :   69 ( 352 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_153,negated_conjecture,(
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

tff(f_94,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_72,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_133,axiom,(
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
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_131,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_44,plain,(
    ! [A_25,F_30,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k1_partfun1(A_25,B_26,C_27,D_28,E_29,F_30),k1_zfmisc_1(k2_zfmisc_1(A_25,D_28)))
      | ~ m1_subset_1(F_30,k1_zfmisc_1(k2_zfmisc_1(C_27,D_28)))
      | ~ v1_funct_1(F_30)
      | ~ m1_subset_1(E_29,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(E_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_71,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_501,plain,(
    ! [D_99,C_100,A_101,B_102] :
      ( D_99 = C_100
      | ~ r2_relset_1(A_101,B_102,C_100,D_99)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_511,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_501])).

tff(c_530,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_511])).

tff(c_864,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_530])).

tff(c_974,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_864])).

tff(c_981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_974])).

tff(c_982,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_1040,plain,(
    ! [B_183,D_184,E_185,A_182,C_186] :
      ( k1_xboole_0 = C_186
      | v2_funct_1(D_184)
      | ~ v2_funct_1(k1_partfun1(A_182,B_183,B_183,C_186,D_184,E_185))
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(B_183,C_186)))
      | ~ v1_funct_2(E_185,B_183,C_186)
      | ~ v1_funct_1(E_185)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_2(D_184,A_182,B_183)
      | ~ v1_funct_1(D_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1042,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_1040])).

tff(c_1044,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_72,c_1042])).

tff(c_1045,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_1044])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1078,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1076,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_1045,c_12])).

tff(c_132,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_139,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_132])).

tff(c_198,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_211,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_139,c_198])).

tff(c_277,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_1194,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1076,c_277])).

tff(c_1199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_1194])).

tff(c_1200,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_1236,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1200,c_60])).

tff(c_1532,plain,(
    ! [D_235,C_236,A_237,B_238] :
      ( D_235 = C_236
      | ~ r2_relset_1(A_237,B_238,C_236,D_235)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1540,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_1532])).

tff(c_1555,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1540])).

tff(c_1590,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1555])).

tff(c_1830,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1590])).

tff(c_1837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_1236,c_1200,c_1830])).

tff(c_1838,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1555])).

tff(c_2243,plain,(
    ! [A_342,E_345,D_344,B_343,C_346] :
      ( k1_xboole_0 = C_346
      | v2_funct_1(D_344)
      | ~ v2_funct_1(k1_partfun1(A_342,B_343,B_343,C_346,D_344,E_345))
      | ~ m1_subset_1(E_345,k1_zfmisc_1(k2_zfmisc_1(B_343,C_346)))
      | ~ v1_funct_2(E_345,B_343,C_346)
      | ~ v1_funct_1(E_345)
      | ~ m1_subset_1(D_344,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343)))
      | ~ v1_funct_2(D_344,A_342,B_343)
      | ~ v1_funct_1(D_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2245,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1838,c_2243])).

tff(c_2247,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_1236,c_1200,c_72,c_2245])).

tff(c_2248,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_2247])).

tff(c_2284,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2248,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2278,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2248,c_2248,c_14])).

tff(c_140,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_132])).

tff(c_210,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_198])).

tff(c_1230,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_2404,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2278,c_1230])).

tff(c_2409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2284,c_2404])).

tff(c_2410,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_2418,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2410,c_66])).

tff(c_2441,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1200,c_60])).

tff(c_2856,plain,(
    ! [C_416,A_415,B_418,F_417,E_419,D_414] :
      ( m1_subset_1(k1_partfun1(A_415,B_418,C_416,D_414,E_419,F_417),k1_zfmisc_1(k2_zfmisc_1(A_415,D_414)))
      | ~ m1_subset_1(F_417,k1_zfmisc_1(k2_zfmisc_1(C_416,D_414)))
      | ~ v1_funct_1(F_417)
      | ~ m1_subset_1(E_419,k1_zfmisc_1(k2_zfmisc_1(A_415,B_418)))
      | ~ v1_funct_1(E_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2681,plain,(
    ! [D_384,C_385,A_386,B_387] :
      ( D_384 = C_385
      | ~ r2_relset_1(A_386,B_387,C_385,D_384)
      | ~ m1_subset_1(D_384,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387)))
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2687,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_2681])).

tff(c_2698,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_2687])).

tff(c_2710,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2698])).

tff(c_2859,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2856,c_2710])).

tff(c_2894,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2418,c_2410,c_64,c_2441,c_1200,c_2859])).

tff(c_2895,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2698])).

tff(c_3293,plain,(
    ! [B_484,C_487,A_483,D_485,E_486] :
      ( k1_xboole_0 = C_487
      | v2_funct_1(D_485)
      | ~ v2_funct_1(k1_partfun1(A_483,B_484,B_484,C_487,D_485,E_486))
      | ~ m1_subset_1(E_486,k1_zfmisc_1(k2_zfmisc_1(B_484,C_487)))
      | ~ v1_funct_2(E_486,B_484,C_487)
      | ~ v1_funct_1(E_486)
      | ~ m1_subset_1(D_485,k1_zfmisc_1(k2_zfmisc_1(A_483,B_484)))
      | ~ v1_funct_2(D_485,A_483,B_484)
      | ~ v1_funct_1(D_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3295,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2895,c_3293])).

tff(c_3297,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2418,c_2410,c_64,c_62,c_2441,c_1200,c_72,c_3295])).

tff(c_3298,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_3297])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2431,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2410,c_10])).

tff(c_2557,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2431])).

tff(c_3321,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_2557])).

tff(c_3328,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_3298,c_14])).

tff(c_3459,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3328,c_2410])).

tff(c_3461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3321,c_3459])).

tff(c_3463,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2431])).

tff(c_92,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_98,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_20])).

tff(c_111,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_72])).

tff(c_3473,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3463,c_111])).

tff(c_3481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_3473])).

tff(c_3482,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3582,plain,(
    ! [C_507,A_508,B_509] :
      ( v1_relat_1(C_507)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(k2_zfmisc_1(A_508,B_509))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3604,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3582])).

tff(c_3616,plain,(
    ! [C_511,B_512,A_513] :
      ( v5_relat_1(C_511,B_512)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(k2_zfmisc_1(A_513,B_512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3639,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_3616])).

tff(c_3796,plain,(
    ! [A_539,B_540,D_541] :
      ( r2_relset_1(A_539,B_540,D_541,D_541)
      | ~ m1_subset_1(D_541,k1_zfmisc_1(k2_zfmisc_1(A_539,B_540))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3811,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_71,c_3796])).

tff(c_3814,plain,(
    ! [A_542,B_543,C_544] :
      ( k2_relset_1(A_542,B_543,C_544) = k2_relat_1(C_544)
      | ~ m1_subset_1(C_544,k1_zfmisc_1(k2_zfmisc_1(A_542,B_543))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3837,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3814])).

tff(c_3856,plain,(
    ! [D_546,C_547,A_548,B_549] :
      ( D_546 = C_547
      | ~ r2_relset_1(A_548,B_549,C_547,D_546)
      | ~ m1_subset_1(D_546,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549)))
      | ~ m1_subset_1(C_547,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3866,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_3856])).

tff(c_3885,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_3866])).

tff(c_3928,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3885])).

tff(c_4278,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_3928])).

tff(c_4285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_4278])).

tff(c_4286,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3885])).

tff(c_4781,plain,(
    ! [A_690,B_691,C_692,D_693] :
      ( k2_relset_1(A_690,B_691,C_692) = B_691
      | ~ r2_relset_1(B_691,B_691,k1_partfun1(B_691,A_690,A_690,B_691,D_693,C_692),k6_partfun1(B_691))
      | ~ m1_subset_1(D_693,k1_zfmisc_1(k2_zfmisc_1(B_691,A_690)))
      | ~ v1_funct_2(D_693,B_691,A_690)
      | ~ v1_funct_1(D_693)
      | ~ m1_subset_1(C_692,k1_zfmisc_1(k2_zfmisc_1(A_690,B_691)))
      | ~ v1_funct_2(C_692,A_690,B_691)
      | ~ v1_funct_1(C_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4784,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4286,c_4781])).

tff(c_4789,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_3811,c_3837,c_4784])).

tff(c_40,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4798,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4789,c_40])).

tff(c_4805,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3604,c_3639,c_4789,c_4798])).

tff(c_4807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3482,c_4805])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:22:10 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.85/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.19  
% 5.85/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.19  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.85/2.19  
% 5.85/2.19  %Foreground sorts:
% 5.85/2.19  
% 5.85/2.19  
% 5.85/2.19  %Background operators:
% 5.85/2.19  
% 5.85/2.19  
% 5.85/2.19  %Foreground operators:
% 5.85/2.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.85/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.85/2.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.85/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.85/2.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.85/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.85/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.85/2.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.85/2.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.85/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.85/2.19  tff('#skF_2', type, '#skF_2': $i).
% 5.85/2.19  tff('#skF_3', type, '#skF_3': $i).
% 5.85/2.19  tff('#skF_1', type, '#skF_1': $i).
% 5.85/2.19  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.85/2.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.85/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.85/2.19  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.85/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.85/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.85/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.85/2.19  tff('#skF_4', type, '#skF_4': $i).
% 5.85/2.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.85/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.85/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.85/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.85/2.19  
% 5.85/2.21  tff(f_153, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 5.85/2.21  tff(f_94, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.85/2.21  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.85/2.21  tff(f_92, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.85/2.21  tff(f_72, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.85/2.21  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.85/2.21  tff(f_133, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 5.85/2.21  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.85/2.21  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.85/2.21  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.85/2.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.85/2.21  tff(f_44, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 5.85/2.21  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.85/2.21  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.85/2.21  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.85/2.21  tff(f_111, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.85/2.21  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.85/2.21  tff(c_56, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.85/2.21  tff(c_131, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 5.85/2.21  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.85/2.21  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.85/2.21  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.85/2.21  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.85/2.21  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.85/2.21  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.85/2.21  tff(c_48, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.85/2.21  tff(c_24, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.85/2.21  tff(c_72, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 5.85/2.21  tff(c_44, plain, (![A_25, F_30, E_29, C_27, D_28, B_26]: (m1_subset_1(k1_partfun1(A_25, B_26, C_27, D_28, E_29, F_30), k1_zfmisc_1(k2_zfmisc_1(A_25, D_28))) | ~m1_subset_1(F_30, k1_zfmisc_1(k2_zfmisc_1(C_27, D_28))) | ~v1_funct_1(F_30) | ~m1_subset_1(E_29, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(E_29))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.85/2.21  tff(c_38, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.85/2.21  tff(c_71, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38])).
% 5.85/2.21  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.85/2.21  tff(c_501, plain, (![D_99, C_100, A_101, B_102]: (D_99=C_100 | ~r2_relset_1(A_101, B_102, C_100, D_99) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.85/2.21  tff(c_511, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_501])).
% 5.85/2.21  tff(c_530, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_511])).
% 5.85/2.21  tff(c_864, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_530])).
% 5.85/2.21  tff(c_974, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_864])).
% 5.85/2.21  tff(c_981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_974])).
% 5.85/2.21  tff(c_982, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_530])).
% 5.85/2.21  tff(c_1040, plain, (![B_183, D_184, E_185, A_182, C_186]: (k1_xboole_0=C_186 | v2_funct_1(D_184) | ~v2_funct_1(k1_partfun1(A_182, B_183, B_183, C_186, D_184, E_185)) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(B_183, C_186))) | ~v1_funct_2(E_185, B_183, C_186) | ~v1_funct_1(E_185) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_2(D_184, A_182, B_183) | ~v1_funct_1(D_184))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.85/2.21  tff(c_1042, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_982, c_1040])).
% 5.85/2.21  tff(c_1044, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_72, c_1042])).
% 5.85/2.21  tff(c_1045, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_131, c_1044])).
% 5.85/2.21  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.85/2.21  tff(c_1078, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_8])).
% 5.85/2.21  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.85/2.21  tff(c_1076, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_1045, c_12])).
% 5.85/2.21  tff(c_132, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.85/2.21  tff(c_139, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_132])).
% 5.85/2.21  tff(c_198, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.85/2.21  tff(c_211, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_139, c_198])).
% 5.85/2.21  tff(c_277, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_211])).
% 5.85/2.21  tff(c_1194, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1076, c_277])).
% 5.85/2.21  tff(c_1199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1078, c_1194])).
% 5.85/2.21  tff(c_1200, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_211])).
% 5.85/2.21  tff(c_1236, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1200, c_60])).
% 5.85/2.21  tff(c_1532, plain, (![D_235, C_236, A_237, B_238]: (D_235=C_236 | ~r2_relset_1(A_237, B_238, C_236, D_235) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.85/2.21  tff(c_1540, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_1532])).
% 5.85/2.21  tff(c_1555, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1540])).
% 5.85/2.21  tff(c_1590, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1555])).
% 5.85/2.21  tff(c_1830, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1590])).
% 5.85/2.21  tff(c_1837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_1236, c_1200, c_1830])).
% 5.85/2.21  tff(c_1838, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1555])).
% 5.85/2.21  tff(c_2243, plain, (![A_342, E_345, D_344, B_343, C_346]: (k1_xboole_0=C_346 | v2_funct_1(D_344) | ~v2_funct_1(k1_partfun1(A_342, B_343, B_343, C_346, D_344, E_345)) | ~m1_subset_1(E_345, k1_zfmisc_1(k2_zfmisc_1(B_343, C_346))) | ~v1_funct_2(E_345, B_343, C_346) | ~v1_funct_1(E_345) | ~m1_subset_1(D_344, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))) | ~v1_funct_2(D_344, A_342, B_343) | ~v1_funct_1(D_344))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.85/2.21  tff(c_2245, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1838, c_2243])).
% 5.85/2.21  tff(c_2247, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_1236, c_1200, c_72, c_2245])).
% 5.85/2.21  tff(c_2248, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_131, c_2247])).
% 5.85/2.21  tff(c_2284, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2248, c_8])).
% 5.85/2.21  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.85/2.21  tff(c_2278, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2248, c_2248, c_14])).
% 5.85/2.21  tff(c_140, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_132])).
% 5.85/2.21  tff(c_210, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_140, c_198])).
% 5.85/2.21  tff(c_1230, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_210])).
% 5.85/2.21  tff(c_2404, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2278, c_1230])).
% 5.85/2.21  tff(c_2409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2284, c_2404])).
% 5.85/2.21  tff(c_2410, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_210])).
% 5.85/2.21  tff(c_2418, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2410, c_66])).
% 5.85/2.21  tff(c_2441, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1200, c_60])).
% 5.85/2.21  tff(c_2856, plain, (![C_416, A_415, B_418, F_417, E_419, D_414]: (m1_subset_1(k1_partfun1(A_415, B_418, C_416, D_414, E_419, F_417), k1_zfmisc_1(k2_zfmisc_1(A_415, D_414))) | ~m1_subset_1(F_417, k1_zfmisc_1(k2_zfmisc_1(C_416, D_414))) | ~v1_funct_1(F_417) | ~m1_subset_1(E_419, k1_zfmisc_1(k2_zfmisc_1(A_415, B_418))) | ~v1_funct_1(E_419))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.85/2.21  tff(c_2681, plain, (![D_384, C_385, A_386, B_387]: (D_384=C_385 | ~r2_relset_1(A_386, B_387, C_385, D_384) | ~m1_subset_1(D_384, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.85/2.21  tff(c_2687, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_2681])).
% 5.85/2.21  tff(c_2698, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_2687])).
% 5.85/2.21  tff(c_2710, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2698])).
% 5.85/2.21  tff(c_2859, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2856, c_2710])).
% 5.85/2.21  tff(c_2894, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_2418, c_2410, c_64, c_2441, c_1200, c_2859])).
% 5.85/2.21  tff(c_2895, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2698])).
% 5.85/2.21  tff(c_3293, plain, (![B_484, C_487, A_483, D_485, E_486]: (k1_xboole_0=C_487 | v2_funct_1(D_485) | ~v2_funct_1(k1_partfun1(A_483, B_484, B_484, C_487, D_485, E_486)) | ~m1_subset_1(E_486, k1_zfmisc_1(k2_zfmisc_1(B_484, C_487))) | ~v1_funct_2(E_486, B_484, C_487) | ~v1_funct_1(E_486) | ~m1_subset_1(D_485, k1_zfmisc_1(k2_zfmisc_1(A_483, B_484))) | ~v1_funct_2(D_485, A_483, B_484) | ~v1_funct_1(D_485))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.85/2.21  tff(c_3295, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2895, c_3293])).
% 5.85/2.21  tff(c_3297, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2418, c_2410, c_64, c_62, c_2441, c_1200, c_72, c_3295])).
% 5.85/2.21  tff(c_3298, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_131, c_3297])).
% 5.85/2.21  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.85/2.21  tff(c_2431, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2410, c_10])).
% 5.85/2.21  tff(c_2557, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_2431])).
% 5.85/2.21  tff(c_3321, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3298, c_2557])).
% 5.85/2.21  tff(c_3328, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3298, c_3298, c_14])).
% 5.85/2.21  tff(c_3459, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3328, c_2410])).
% 5.85/2.21  tff(c_3461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3321, c_3459])).
% 5.85/2.21  tff(c_3463, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2431])).
% 5.85/2.21  tff(c_92, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.85/2.21  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.85/2.21  tff(c_98, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92, c_20])).
% 5.85/2.21  tff(c_111, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_72])).
% 5.85/2.21  tff(c_3473, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3463, c_111])).
% 5.85/2.21  tff(c_3481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_3473])).
% 5.85/2.21  tff(c_3482, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 5.85/2.21  tff(c_3582, plain, (![C_507, A_508, B_509]: (v1_relat_1(C_507) | ~m1_subset_1(C_507, k1_zfmisc_1(k2_zfmisc_1(A_508, B_509))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.85/2.21  tff(c_3604, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_3582])).
% 5.85/2.21  tff(c_3616, plain, (![C_511, B_512, A_513]: (v5_relat_1(C_511, B_512) | ~m1_subset_1(C_511, k1_zfmisc_1(k2_zfmisc_1(A_513, B_512))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.85/2.21  tff(c_3639, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_3616])).
% 5.85/2.21  tff(c_3796, plain, (![A_539, B_540, D_541]: (r2_relset_1(A_539, B_540, D_541, D_541) | ~m1_subset_1(D_541, k1_zfmisc_1(k2_zfmisc_1(A_539, B_540))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.85/2.21  tff(c_3811, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_71, c_3796])).
% 5.85/2.21  tff(c_3814, plain, (![A_542, B_543, C_544]: (k2_relset_1(A_542, B_543, C_544)=k2_relat_1(C_544) | ~m1_subset_1(C_544, k1_zfmisc_1(k2_zfmisc_1(A_542, B_543))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.85/2.21  tff(c_3837, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_3814])).
% 5.85/2.21  tff(c_3856, plain, (![D_546, C_547, A_548, B_549]: (D_546=C_547 | ~r2_relset_1(A_548, B_549, C_547, D_546) | ~m1_subset_1(D_546, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))) | ~m1_subset_1(C_547, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.85/2.21  tff(c_3866, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_3856])).
% 5.85/2.21  tff(c_3885, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_3866])).
% 5.85/2.21  tff(c_3928, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3885])).
% 5.85/2.21  tff(c_4278, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_3928])).
% 5.85/2.21  tff(c_4285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_4278])).
% 5.85/2.21  tff(c_4286, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3885])).
% 5.85/2.21  tff(c_4781, plain, (![A_690, B_691, C_692, D_693]: (k2_relset_1(A_690, B_691, C_692)=B_691 | ~r2_relset_1(B_691, B_691, k1_partfun1(B_691, A_690, A_690, B_691, D_693, C_692), k6_partfun1(B_691)) | ~m1_subset_1(D_693, k1_zfmisc_1(k2_zfmisc_1(B_691, A_690))) | ~v1_funct_2(D_693, B_691, A_690) | ~v1_funct_1(D_693) | ~m1_subset_1(C_692, k1_zfmisc_1(k2_zfmisc_1(A_690, B_691))) | ~v1_funct_2(C_692, A_690, B_691) | ~v1_funct_1(C_692))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.85/2.21  tff(c_4784, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4286, c_4781])).
% 5.85/2.21  tff(c_4789, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_3811, c_3837, c_4784])).
% 5.85/2.21  tff(c_40, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.85/2.21  tff(c_4798, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4789, c_40])).
% 5.85/2.21  tff(c_4805, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3604, c_3639, c_4789, c_4798])).
% 5.85/2.21  tff(c_4807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3482, c_4805])).
% 5.85/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.21  
% 5.85/2.21  Inference rules
% 5.85/2.21  ----------------------
% 5.85/2.21  #Ref     : 0
% 5.85/2.21  #Sup     : 1038
% 5.85/2.21  #Fact    : 0
% 5.85/2.21  #Define  : 0
% 5.85/2.22  #Split   : 24
% 5.85/2.22  #Chain   : 0
% 5.85/2.22  #Close   : 0
% 5.85/2.22  
% 5.85/2.22  Ordering : KBO
% 5.85/2.22  
% 5.85/2.22  Simplification rules
% 5.85/2.22  ----------------------
% 5.85/2.22  #Subsume      : 92
% 5.85/2.22  #Demod        : 868
% 5.85/2.22  #Tautology    : 487
% 5.85/2.22  #SimpNegUnit  : 7
% 5.85/2.22  #BackRed      : 143
% 5.85/2.22  
% 5.85/2.22  #Partial instantiations: 0
% 5.85/2.22  #Strategies tried      : 1
% 5.85/2.22  
% 5.85/2.22  Timing (in seconds)
% 5.85/2.22  ----------------------
% 5.85/2.22  Preprocessing        : 0.36
% 5.85/2.22  Parsing              : 0.19
% 5.85/2.22  CNF conversion       : 0.02
% 5.85/2.22  Main loop            : 1.03
% 5.85/2.22  Inferencing          : 0.36
% 5.85/2.22  Reduction            : 0.36
% 5.85/2.22  Demodulation         : 0.26
% 5.85/2.22  BG Simplification    : 0.04
% 5.85/2.22  Subsumption          : 0.17
% 5.85/2.22  Abstraction          : 0.04
% 5.85/2.22  MUC search           : 0.00
% 5.85/2.22  Cooper               : 0.00
% 5.85/2.22  Total                : 1.44
% 5.85/2.22  Index Insertion      : 0.00
% 5.85/2.22  Index Deletion       : 0.00
% 5.85/2.22  Index Matching       : 0.00
% 5.85/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
