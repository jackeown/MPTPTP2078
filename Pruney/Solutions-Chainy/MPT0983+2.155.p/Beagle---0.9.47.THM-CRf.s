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
% DateTime   : Thu Dec  3 10:12:24 EST 2020

% Result     : Theorem 8.28s
% Output     : CNFRefutation 8.65s
% Verified   : 
% Statistics : Number of formulae       :  189 (1428 expanded)
%              Number of leaves         :   43 ( 501 expanded)
%              Depth                    :   11
%              Number of atoms          :  371 (4266 expanded)
%              Number of equality atoms :   99 ( 790 expanded)
%              Maximal formula depth    :   15 (   3 average)
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

tff(f_99,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_57,axiom,(
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

tff(f_53,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

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

tff(c_58,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_139,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_46,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_73,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_40])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_618,plain,(
    ! [D_115,C_116,A_117,B_118] :
      ( D_115 = C_116
      | ~ r2_relset_1(A_117,B_118,C_116,D_115)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_628,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_618])).

tff(c_647,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_628])).

tff(c_668,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_1043,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_668])).

tff(c_1050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_1043])).

tff(c_1051,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_1513,plain,(
    ! [D_253,C_252,B_251,E_250,A_249] :
      ( k1_xboole_0 = C_252
      | v2_funct_1(D_253)
      | ~ v2_funct_1(k1_partfun1(A_249,B_251,B_251,C_252,D_253,E_250))
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(B_251,C_252)))
      | ~ v1_funct_2(E_250,B_251,C_252)
      | ~ v1_funct_1(E_250)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(A_249,B_251)))
      | ~ v1_funct_2(D_253,A_249,B_251)
      | ~ v1_funct_1(D_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1515,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1051,c_1513])).

tff(c_1517,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_74,c_1515])).

tff(c_1518,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_1517])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1552,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1550,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_1518,c_12])).

tff(c_158,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_158])).

tff(c_196,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_209,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_178,c_196])).

tff(c_401,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_1683,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1550,c_401])).

tff(c_1688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_1683])).

tff(c_1689,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_1721,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1689,c_62])).

tff(c_2964,plain,(
    ! [D_436,C_437,A_438,B_439] :
      ( D_436 = C_437
      | ~ r2_relset_1(A_438,B_439,C_437,D_436)
      | ~ m1_subset_1(D_436,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439)))
      | ~ m1_subset_1(C_437,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2972,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_2964])).

tff(c_2987,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_2972])).

tff(c_3036,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2987])).

tff(c_3287,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_3036])).

tff(c_3294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_1721,c_1689,c_3287])).

tff(c_3295,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2987])).

tff(c_3666,plain,(
    ! [B_541,A_539,E_540,D_543,C_542] :
      ( k1_xboole_0 = C_542
      | v2_funct_1(D_543)
      | ~ v2_funct_1(k1_partfun1(A_539,B_541,B_541,C_542,D_543,E_540))
      | ~ m1_subset_1(E_540,k1_zfmisc_1(k2_zfmisc_1(B_541,C_542)))
      | ~ v1_funct_2(E_540,B_541,C_542)
      | ~ v1_funct_1(E_540)
      | ~ m1_subset_1(D_543,k1_zfmisc_1(k2_zfmisc_1(A_539,B_541)))
      | ~ v1_funct_2(D_543,A_539,B_541)
      | ~ v1_funct_1(D_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_3668,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3295,c_3666])).

tff(c_3670,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_1721,c_1689,c_74,c_3668])).

tff(c_3671,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_3670])).

tff(c_3705,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3671,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3701,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3671,c_3671,c_14])).

tff(c_179,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_158])).

tff(c_208,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_179,c_196])).

tff(c_364,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_3828,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3701,c_364])).

tff(c_3833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3705,c_3828])).

tff(c_3834,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_3838,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3834,c_68])).

tff(c_5288,plain,(
    ! [D_751,C_752,A_753,B_754] :
      ( D_751 = C_752
      | ~ r2_relset_1(A_753,B_754,C_752,D_751)
      | ~ m1_subset_1(D_751,k1_zfmisc_1(k2_zfmisc_1(A_753,B_754)))
      | ~ m1_subset_1(C_752,k1_zfmisc_1(k2_zfmisc_1(A_753,B_754))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5296,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_5288])).

tff(c_5311,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_5296])).

tff(c_5334,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5311])).

tff(c_5666,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_5334])).

tff(c_5673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3838,c_3834,c_66,c_62,c_5666])).

tff(c_5674,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5311])).

tff(c_6053,plain,(
    ! [C_870,D_871,B_869,E_868,A_867] :
      ( k1_xboole_0 = C_870
      | v2_funct_1(D_871)
      | ~ v2_funct_1(k1_partfun1(A_867,B_869,B_869,C_870,D_871,E_868))
      | ~ m1_subset_1(E_868,k1_zfmisc_1(k2_zfmisc_1(B_869,C_870)))
      | ~ v1_funct_2(E_868,B_869,C_870)
      | ~ v1_funct_1(E_868)
      | ~ m1_subset_1(D_871,k1_zfmisc_1(k2_zfmisc_1(A_867,B_869)))
      | ~ v1_funct_2(D_871,A_867,B_869)
      | ~ v1_funct_1(D_871) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_6055,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5674,c_6053])).

tff(c_6057,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_3838,c_3834,c_66,c_64,c_62,c_74,c_6055])).

tff(c_6058,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_6057])).

tff(c_6094,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6058,c_8])).

tff(c_6092,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6058,c_6058,c_12])).

tff(c_3867,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_6257,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6092,c_3867])).

tff(c_6262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6094,c_6257])).

tff(c_6263,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_6266,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6263,c_62])).

tff(c_6723,plain,(
    ! [C_952,E_954,B_955,F_951,D_953,A_956] :
      ( m1_subset_1(k1_partfun1(A_956,B_955,C_952,D_953,E_954,F_951),k1_zfmisc_1(k2_zfmisc_1(A_956,D_953)))
      | ~ m1_subset_1(F_951,k1_zfmisc_1(k2_zfmisc_1(C_952,D_953)))
      | ~ v1_funct_1(F_951)
      | ~ m1_subset_1(E_954,k1_zfmisc_1(k2_zfmisc_1(A_956,B_955)))
      | ~ v1_funct_1(E_954) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6543,plain,(
    ! [D_921,C_922,A_923,B_924] :
      ( D_921 = C_922
      | ~ r2_relset_1(A_923,B_924,C_922,D_921)
      | ~ m1_subset_1(D_921,k1_zfmisc_1(k2_zfmisc_1(A_923,B_924)))
      | ~ m1_subset_1(C_922,k1_zfmisc_1(k2_zfmisc_1(A_923,B_924))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6549,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_6543])).

tff(c_6560,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_6549])).

tff(c_6611,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6560])).

tff(c_6726,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6723,c_6611])).

tff(c_6761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3838,c_3834,c_66,c_6266,c_6263,c_6726])).

tff(c_6762,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_6560])).

tff(c_7175,plain,(
    ! [D_1021,E_1018,C_1020,B_1019,A_1017] :
      ( k1_xboole_0 = C_1020
      | v2_funct_1(D_1021)
      | ~ v2_funct_1(k1_partfun1(A_1017,B_1019,B_1019,C_1020,D_1021,E_1018))
      | ~ m1_subset_1(E_1018,k1_zfmisc_1(k2_zfmisc_1(B_1019,C_1020)))
      | ~ v1_funct_2(E_1018,B_1019,C_1020)
      | ~ v1_funct_1(E_1018)
      | ~ m1_subset_1(D_1021,k1_zfmisc_1(k2_zfmisc_1(A_1017,B_1019)))
      | ~ v1_funct_2(D_1021,A_1017,B_1019)
      | ~ v1_funct_1(D_1021) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_7177,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6762,c_7175])).

tff(c_7179,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_3838,c_3834,c_66,c_64,c_6266,c_6263,c_74,c_7177])).

tff(c_7180,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_7179])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6277,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6263,c_10])).

tff(c_6297,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6277])).

tff(c_7203,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7180,c_6297])).

tff(c_7361,plain,(
    ! [A_1036] : k2_zfmisc_1(A_1036,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7180,c_7180,c_12])).

tff(c_7404,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7361,c_6263])).

tff(c_7433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7203,c_7404])).

tff(c_7435,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6277])).

tff(c_115,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_121,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_24])).

tff(c_134,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_74])).

tff(c_7443,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7435,c_134])).

tff(c_3849,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3834,c_10])).

tff(c_7500,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4'
    | '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7435,c_7435,c_7435,c_3849])).

tff(c_7501,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7500])).

tff(c_7447,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7435,c_7435,c_12])).

tff(c_7445,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7435,c_7435,c_14])).

tff(c_7434,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6277])).

tff(c_7541,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7435,c_7435,c_7434])).

tff(c_7542,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7541])).

tff(c_7544,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7542,c_3834])).

tff(c_7637,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7445,c_7544])).

tff(c_7638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7501,c_7637])).

tff(c_7639,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7541])).

tff(c_7643,plain,(
    k2_zfmisc_1('#skF_1','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7639,c_3834])).

tff(c_7741,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7447,c_7643])).

tff(c_7742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7501,c_7741])).

tff(c_7744,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7500])).

tff(c_7751,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7744,c_139])).

tff(c_7758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7443,c_7751])).

tff(c_7759,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_7795,plain,(
    ! [B_1058,A_1059] :
      ( v1_relat_1(B_1058)
      | ~ m1_subset_1(B_1058,k1_zfmisc_1(A_1059))
      | ~ v1_relat_1(A_1059) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7807,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_7795])).

tff(c_7817,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7807])).

tff(c_7917,plain,(
    ! [C_1068,B_1069,A_1070] :
      ( v5_relat_1(C_1068,B_1069)
      | ~ m1_subset_1(C_1068,k1_zfmisc_1(k2_zfmisc_1(A_1070,B_1069))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7940,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_7917])).

tff(c_8097,plain,(
    ! [A_1097,B_1098,D_1099] :
      ( r2_relset_1(A_1097,B_1098,D_1099,D_1099)
      | ~ m1_subset_1(D_1099,k1_zfmisc_1(k2_zfmisc_1(A_1097,B_1098))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8111,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_73,c_8097])).

tff(c_8175,plain,(
    ! [A_1106,B_1107,C_1108] :
      ( k2_relset_1(A_1106,B_1107,C_1108) = k2_relat_1(C_1108)
      | ~ m1_subset_1(C_1108,k1_zfmisc_1(k2_zfmisc_1(A_1106,B_1107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8198,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_8175])).

tff(c_8208,plain,(
    ! [D_1109,C_1110,A_1111,B_1112] :
      ( D_1109 = C_1110
      | ~ r2_relset_1(A_1111,B_1112,C_1110,D_1109)
      | ~ m1_subset_1(D_1109,k1_zfmisc_1(k2_zfmisc_1(A_1111,B_1112)))
      | ~ m1_subset_1(C_1110,k1_zfmisc_1(k2_zfmisc_1(A_1111,B_1112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8218,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_8208])).

tff(c_8237,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_8218])).

tff(c_8559,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8237])).

tff(c_8652,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_8559])).

tff(c_8659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_8652])).

tff(c_8660,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_8237])).

tff(c_8806,plain,(
    ! [A_1209,B_1210,C_1211,D_1212] :
      ( k2_relset_1(A_1209,B_1210,C_1211) = B_1210
      | ~ r2_relset_1(B_1210,B_1210,k1_partfun1(B_1210,A_1209,A_1209,B_1210,D_1212,C_1211),k6_partfun1(B_1210))
      | ~ m1_subset_1(D_1212,k1_zfmisc_1(k2_zfmisc_1(B_1210,A_1209)))
      | ~ v1_funct_2(D_1212,B_1210,A_1209)
      | ~ v1_funct_1(D_1212)
      | ~ m1_subset_1(C_1211,k1_zfmisc_1(k2_zfmisc_1(A_1209,B_1210)))
      | ~ v1_funct_2(C_1211,A_1209,B_1210)
      | ~ v1_funct_1(C_1211) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8809,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8660,c_8806])).

tff(c_8814,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_8111,c_8198,c_8809])).

tff(c_42,plain,(
    ! [B_26] :
      ( v2_funct_2(B_26,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8823,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8814,c_42])).

tff(c_8830,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7817,c_7940,c_8814,c_8823])).

tff(c_8832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7759,c_8830])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.28/2.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.42/2.90  
% 8.42/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.42/2.90  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.42/2.90  
% 8.42/2.90  %Foreground sorts:
% 8.42/2.90  
% 8.42/2.90  
% 8.42/2.90  %Background operators:
% 8.42/2.90  
% 8.42/2.90  
% 8.42/2.90  %Foreground operators:
% 8.42/2.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.42/2.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.42/2.90  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.42/2.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.42/2.90  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.42/2.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.42/2.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.42/2.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.42/2.90  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.42/2.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.42/2.90  tff('#skF_2', type, '#skF_2': $i).
% 8.42/2.90  tff('#skF_3', type, '#skF_3': $i).
% 8.42/2.90  tff('#skF_1', type, '#skF_1': $i).
% 8.42/2.90  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 8.42/2.90  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.42/2.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.42/2.90  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.42/2.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.42/2.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.42/2.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.42/2.90  tff('#skF_4', type, '#skF_4': $i).
% 8.42/2.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.42/2.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.42/2.90  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.42/2.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.42/2.90  
% 8.65/2.94  tff(f_158, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 8.65/2.94  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.65/2.94  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.65/2.94  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.65/2.94  tff(f_77, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 8.65/2.94  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.65/2.94  tff(f_138, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 8.65/2.94  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.65/2.94  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.65/2.94  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.65/2.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.65/2.94  tff(f_53, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 8.65/2.94  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.65/2.94  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.65/2.94  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.65/2.94  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.65/2.94  tff(f_116, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 8.65/2.94  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 8.65/2.94  tff(c_58, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.65/2.94  tff(c_139, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 8.65/2.94  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.65/2.94  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.65/2.94  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.65/2.94  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.65/2.94  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.65/2.94  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.65/2.94  tff(c_50, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.65/2.94  tff(c_28, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.65/2.94  tff(c_74, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28])).
% 8.65/2.94  tff(c_46, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.65/2.94  tff(c_40, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.65/2.94  tff(c_73, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_40])).
% 8.65/2.94  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.65/2.94  tff(c_618, plain, (![D_115, C_116, A_117, B_118]: (D_115=C_116 | ~r2_relset_1(A_117, B_118, C_116, D_115) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.65/2.94  tff(c_628, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_618])).
% 8.65/2.94  tff(c_647, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_628])).
% 8.65/2.94  tff(c_668, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_647])).
% 8.65/2.94  tff(c_1043, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_668])).
% 8.65/2.94  tff(c_1050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_1043])).
% 8.65/2.94  tff(c_1051, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_647])).
% 8.65/2.94  tff(c_1513, plain, (![D_253, C_252, B_251, E_250, A_249]: (k1_xboole_0=C_252 | v2_funct_1(D_253) | ~v2_funct_1(k1_partfun1(A_249, B_251, B_251, C_252, D_253, E_250)) | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(B_251, C_252))) | ~v1_funct_2(E_250, B_251, C_252) | ~v1_funct_1(E_250) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(A_249, B_251))) | ~v1_funct_2(D_253, A_249, B_251) | ~v1_funct_1(D_253))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.65/2.94  tff(c_1515, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1051, c_1513])).
% 8.65/2.94  tff(c_1517, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_74, c_1515])).
% 8.65/2.94  tff(c_1518, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_139, c_1517])).
% 8.65/2.94  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.65/2.94  tff(c_1552, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_8])).
% 8.65/2.94  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.65/2.94  tff(c_1550, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_1518, c_12])).
% 8.65/2.94  tff(c_158, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.65/2.94  tff(c_178, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_158])).
% 8.65/2.94  tff(c_196, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.65/2.94  tff(c_209, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(resolution, [status(thm)], [c_178, c_196])).
% 8.65/2.94  tff(c_401, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_209])).
% 8.65/2.94  tff(c_1683, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1550, c_401])).
% 8.65/2.94  tff(c_1688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1552, c_1683])).
% 8.65/2.94  tff(c_1689, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_209])).
% 8.65/2.94  tff(c_1721, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1689, c_62])).
% 8.65/2.94  tff(c_2964, plain, (![D_436, C_437, A_438, B_439]: (D_436=C_437 | ~r2_relset_1(A_438, B_439, C_437, D_436) | ~m1_subset_1(D_436, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))) | ~m1_subset_1(C_437, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.65/2.94  tff(c_2972, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_2964])).
% 8.65/2.94  tff(c_2987, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_2972])).
% 8.65/2.94  tff(c_3036, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2987])).
% 8.65/2.94  tff(c_3287, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_3036])).
% 8.65/2.94  tff(c_3294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_1721, c_1689, c_3287])).
% 8.65/2.94  tff(c_3295, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2987])).
% 8.65/2.94  tff(c_3666, plain, (![B_541, A_539, E_540, D_543, C_542]: (k1_xboole_0=C_542 | v2_funct_1(D_543) | ~v2_funct_1(k1_partfun1(A_539, B_541, B_541, C_542, D_543, E_540)) | ~m1_subset_1(E_540, k1_zfmisc_1(k2_zfmisc_1(B_541, C_542))) | ~v1_funct_2(E_540, B_541, C_542) | ~v1_funct_1(E_540) | ~m1_subset_1(D_543, k1_zfmisc_1(k2_zfmisc_1(A_539, B_541))) | ~v1_funct_2(D_543, A_539, B_541) | ~v1_funct_1(D_543))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.65/2.94  tff(c_3668, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3295, c_3666])).
% 8.65/2.94  tff(c_3670, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_1721, c_1689, c_74, c_3668])).
% 8.65/2.94  tff(c_3671, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_139, c_3670])).
% 8.65/2.94  tff(c_3705, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3671, c_8])).
% 8.65/2.94  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.65/2.94  tff(c_3701, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3671, c_3671, c_14])).
% 8.65/2.94  tff(c_179, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_158])).
% 8.65/2.94  tff(c_208, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_179, c_196])).
% 8.65/2.94  tff(c_364, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_208])).
% 8.65/2.94  tff(c_3828, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3701, c_364])).
% 8.65/2.94  tff(c_3833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3705, c_3828])).
% 8.65/2.94  tff(c_3834, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_208])).
% 8.65/2.94  tff(c_3838, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3834, c_68])).
% 8.65/2.94  tff(c_5288, plain, (![D_751, C_752, A_753, B_754]: (D_751=C_752 | ~r2_relset_1(A_753, B_754, C_752, D_751) | ~m1_subset_1(D_751, k1_zfmisc_1(k2_zfmisc_1(A_753, B_754))) | ~m1_subset_1(C_752, k1_zfmisc_1(k2_zfmisc_1(A_753, B_754))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.65/2.94  tff(c_5296, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_5288])).
% 8.65/2.94  tff(c_5311, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_5296])).
% 8.65/2.94  tff(c_5334, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5311])).
% 8.65/2.94  tff(c_5666, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_5334])).
% 8.65/2.94  tff(c_5673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_3838, c_3834, c_66, c_62, c_5666])).
% 8.65/2.94  tff(c_5674, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5311])).
% 8.65/2.94  tff(c_6053, plain, (![C_870, D_871, B_869, E_868, A_867]: (k1_xboole_0=C_870 | v2_funct_1(D_871) | ~v2_funct_1(k1_partfun1(A_867, B_869, B_869, C_870, D_871, E_868)) | ~m1_subset_1(E_868, k1_zfmisc_1(k2_zfmisc_1(B_869, C_870))) | ~v1_funct_2(E_868, B_869, C_870) | ~v1_funct_1(E_868) | ~m1_subset_1(D_871, k1_zfmisc_1(k2_zfmisc_1(A_867, B_869))) | ~v1_funct_2(D_871, A_867, B_869) | ~v1_funct_1(D_871))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.65/2.94  tff(c_6055, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5674, c_6053])).
% 8.65/2.94  tff(c_6057, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_3838, c_3834, c_66, c_64, c_62, c_74, c_6055])).
% 8.65/2.94  tff(c_6058, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_139, c_6057])).
% 8.65/2.94  tff(c_6094, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_6058, c_8])).
% 8.65/2.94  tff(c_6092, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6058, c_6058, c_12])).
% 8.65/2.94  tff(c_3867, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_209])).
% 8.65/2.94  tff(c_6257, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6092, c_3867])).
% 8.65/2.94  tff(c_6262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6094, c_6257])).
% 8.65/2.94  tff(c_6263, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_209])).
% 8.65/2.94  tff(c_6266, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6263, c_62])).
% 8.65/2.94  tff(c_6723, plain, (![C_952, E_954, B_955, F_951, D_953, A_956]: (m1_subset_1(k1_partfun1(A_956, B_955, C_952, D_953, E_954, F_951), k1_zfmisc_1(k2_zfmisc_1(A_956, D_953))) | ~m1_subset_1(F_951, k1_zfmisc_1(k2_zfmisc_1(C_952, D_953))) | ~v1_funct_1(F_951) | ~m1_subset_1(E_954, k1_zfmisc_1(k2_zfmisc_1(A_956, B_955))) | ~v1_funct_1(E_954))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.65/2.94  tff(c_6543, plain, (![D_921, C_922, A_923, B_924]: (D_921=C_922 | ~r2_relset_1(A_923, B_924, C_922, D_921) | ~m1_subset_1(D_921, k1_zfmisc_1(k2_zfmisc_1(A_923, B_924))) | ~m1_subset_1(C_922, k1_zfmisc_1(k2_zfmisc_1(A_923, B_924))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.65/2.94  tff(c_6549, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_6543])).
% 8.65/2.94  tff(c_6560, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_6549])).
% 8.65/2.94  tff(c_6611, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_6560])).
% 8.65/2.94  tff(c_6726, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6723, c_6611])).
% 8.65/2.94  tff(c_6761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_3838, c_3834, c_66, c_6266, c_6263, c_6726])).
% 8.65/2.94  tff(c_6762, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_6560])).
% 8.65/2.94  tff(c_7175, plain, (![D_1021, E_1018, C_1020, B_1019, A_1017]: (k1_xboole_0=C_1020 | v2_funct_1(D_1021) | ~v2_funct_1(k1_partfun1(A_1017, B_1019, B_1019, C_1020, D_1021, E_1018)) | ~m1_subset_1(E_1018, k1_zfmisc_1(k2_zfmisc_1(B_1019, C_1020))) | ~v1_funct_2(E_1018, B_1019, C_1020) | ~v1_funct_1(E_1018) | ~m1_subset_1(D_1021, k1_zfmisc_1(k2_zfmisc_1(A_1017, B_1019))) | ~v1_funct_2(D_1021, A_1017, B_1019) | ~v1_funct_1(D_1021))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.65/2.94  tff(c_7177, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6762, c_7175])).
% 8.65/2.94  tff(c_7179, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_3838, c_3834, c_66, c_64, c_6266, c_6263, c_74, c_7177])).
% 8.65/2.94  tff(c_7180, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_139, c_7179])).
% 8.65/2.94  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.65/2.94  tff(c_6277, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6263, c_10])).
% 8.65/2.94  tff(c_6297, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_6277])).
% 8.65/2.94  tff(c_7203, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7180, c_6297])).
% 8.65/2.94  tff(c_7361, plain, (![A_1036]: (k2_zfmisc_1(A_1036, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7180, c_7180, c_12])).
% 8.65/2.94  tff(c_7404, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_7361, c_6263])).
% 8.65/2.94  tff(c_7433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7203, c_7404])).
% 8.65/2.94  tff(c_7435, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_6277])).
% 8.65/2.94  tff(c_115, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.65/2.94  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.65/2.94  tff(c_121, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_115, c_24])).
% 8.65/2.94  tff(c_134, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_121, c_74])).
% 8.65/2.94  tff(c_7443, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7435, c_134])).
% 8.65/2.94  tff(c_3849, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3834, c_10])).
% 8.65/2.94  tff(c_7500, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4' | '#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7435, c_7435, c_7435, c_3849])).
% 8.65/2.94  tff(c_7501, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_7500])).
% 8.65/2.94  tff(c_7447, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7435, c_7435, c_12])).
% 8.65/2.94  tff(c_7445, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7435, c_7435, c_14])).
% 8.65/2.94  tff(c_7434, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_6277])).
% 8.65/2.94  tff(c_7541, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7435, c_7435, c_7434])).
% 8.65/2.94  tff(c_7542, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_7541])).
% 8.65/2.94  tff(c_7544, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7542, c_3834])).
% 8.65/2.94  tff(c_7637, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7445, c_7544])).
% 8.65/2.94  tff(c_7638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7501, c_7637])).
% 8.65/2.94  tff(c_7639, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_7541])).
% 8.65/2.94  tff(c_7643, plain, (k2_zfmisc_1('#skF_1', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7639, c_3834])).
% 8.65/2.94  tff(c_7741, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7447, c_7643])).
% 8.65/2.94  tff(c_7742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7501, c_7741])).
% 8.65/2.94  tff(c_7744, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_7500])).
% 8.65/2.94  tff(c_7751, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7744, c_139])).
% 8.65/2.94  tff(c_7758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7443, c_7751])).
% 8.65/2.94  tff(c_7759, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 8.65/2.94  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.65/2.94  tff(c_7795, plain, (![B_1058, A_1059]: (v1_relat_1(B_1058) | ~m1_subset_1(B_1058, k1_zfmisc_1(A_1059)) | ~v1_relat_1(A_1059))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.65/2.94  tff(c_7807, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_7795])).
% 8.65/2.94  tff(c_7817, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7807])).
% 8.65/2.94  tff(c_7917, plain, (![C_1068, B_1069, A_1070]: (v5_relat_1(C_1068, B_1069) | ~m1_subset_1(C_1068, k1_zfmisc_1(k2_zfmisc_1(A_1070, B_1069))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.65/2.94  tff(c_7940, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_7917])).
% 8.65/2.94  tff(c_8097, plain, (![A_1097, B_1098, D_1099]: (r2_relset_1(A_1097, B_1098, D_1099, D_1099) | ~m1_subset_1(D_1099, k1_zfmisc_1(k2_zfmisc_1(A_1097, B_1098))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.65/2.94  tff(c_8111, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_73, c_8097])).
% 8.65/2.94  tff(c_8175, plain, (![A_1106, B_1107, C_1108]: (k2_relset_1(A_1106, B_1107, C_1108)=k2_relat_1(C_1108) | ~m1_subset_1(C_1108, k1_zfmisc_1(k2_zfmisc_1(A_1106, B_1107))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.65/2.94  tff(c_8198, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_8175])).
% 8.65/2.94  tff(c_8208, plain, (![D_1109, C_1110, A_1111, B_1112]: (D_1109=C_1110 | ~r2_relset_1(A_1111, B_1112, C_1110, D_1109) | ~m1_subset_1(D_1109, k1_zfmisc_1(k2_zfmisc_1(A_1111, B_1112))) | ~m1_subset_1(C_1110, k1_zfmisc_1(k2_zfmisc_1(A_1111, B_1112))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.65/2.94  tff(c_8218, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_8208])).
% 8.65/2.94  tff(c_8237, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_8218])).
% 8.65/2.94  tff(c_8559, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_8237])).
% 8.65/2.94  tff(c_8652, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_8559])).
% 8.65/2.94  tff(c_8659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_8652])).
% 8.65/2.94  tff(c_8660, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_8237])).
% 8.65/2.94  tff(c_8806, plain, (![A_1209, B_1210, C_1211, D_1212]: (k2_relset_1(A_1209, B_1210, C_1211)=B_1210 | ~r2_relset_1(B_1210, B_1210, k1_partfun1(B_1210, A_1209, A_1209, B_1210, D_1212, C_1211), k6_partfun1(B_1210)) | ~m1_subset_1(D_1212, k1_zfmisc_1(k2_zfmisc_1(B_1210, A_1209))) | ~v1_funct_2(D_1212, B_1210, A_1209) | ~v1_funct_1(D_1212) | ~m1_subset_1(C_1211, k1_zfmisc_1(k2_zfmisc_1(A_1209, B_1210))) | ~v1_funct_2(C_1211, A_1209, B_1210) | ~v1_funct_1(C_1211))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.65/2.94  tff(c_8809, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8660, c_8806])).
% 8.65/2.94  tff(c_8814, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_8111, c_8198, c_8809])).
% 8.65/2.94  tff(c_42, plain, (![B_26]: (v2_funct_2(B_26, k2_relat_1(B_26)) | ~v5_relat_1(B_26, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.65/2.94  tff(c_8823, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8814, c_42])).
% 8.65/2.94  tff(c_8830, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7817, c_7940, c_8814, c_8823])).
% 8.65/2.94  tff(c_8832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7759, c_8830])).
% 8.65/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.65/2.94  
% 8.65/2.94  Inference rules
% 8.65/2.94  ----------------------
% 8.65/2.94  #Ref     : 0
% 8.65/2.94  #Sup     : 1933
% 8.65/2.94  #Fact    : 0
% 8.65/2.94  #Define  : 0
% 8.65/2.94  #Split   : 37
% 8.65/2.94  #Chain   : 0
% 8.65/2.94  #Close   : 0
% 8.65/2.94  
% 8.65/2.94  Ordering : KBO
% 8.65/2.94  
% 8.65/2.94  Simplification rules
% 8.65/2.94  ----------------------
% 8.65/2.94  #Subsume      : 165
% 8.65/2.94  #Demod        : 1829
% 8.65/2.94  #Tautology    : 946
% 8.65/2.94  #SimpNegUnit  : 15
% 8.65/2.94  #BackRed      : 311
% 8.65/2.94  
% 8.65/2.94  #Partial instantiations: 0
% 8.65/2.94  #Strategies tried      : 1
% 8.65/2.94  
% 8.65/2.94  Timing (in seconds)
% 8.65/2.94  ----------------------
% 8.65/2.94  Preprocessing        : 0.38
% 8.65/2.94  Parsing              : 0.21
% 8.65/2.94  CNF conversion       : 0.03
% 8.65/2.94  Main loop            : 1.69
% 8.65/2.94  Inferencing          : 0.57
% 8.65/2.94  Reduction            : 0.63
% 8.65/2.94  Demodulation         : 0.46
% 8.65/2.94  BG Simplification    : 0.06
% 8.65/2.94  Subsumption          : 0.28
% 8.65/2.94  Abstraction          : 0.06
% 8.65/2.94  MUC search           : 0.00
% 8.65/2.94  Cooper               : 0.00
% 8.65/2.94  Total                : 2.14
% 8.69/2.94  Index Insertion      : 0.00
% 8.69/2.95  Index Deletion       : 0.00
% 8.69/2.95  Index Matching       : 0.00
% 8.69/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
