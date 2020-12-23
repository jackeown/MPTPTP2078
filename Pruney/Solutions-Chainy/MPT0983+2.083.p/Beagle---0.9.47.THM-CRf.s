%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:13 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 940 expanded)
%              Number of leaves         :   45 ( 333 expanded)
%              Depth                    :   12
%              Number of atoms          :  245 (2477 expanded)
%              Number of equality atoms :   54 ( 333 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_103,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_77,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
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

tff(f_85,axiom,(
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

tff(c_94,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

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
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_67,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_36,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1(k1_partfun1(A_28,B_29,C_30,D_31,E_32,F_33),k1_zfmisc_1(k2_zfmisc_1(A_28,D_31)))
      | ~ m1_subset_1(F_33,k1_zfmisc_1(k2_zfmisc_1(C_30,D_31)))
      | ~ v1_funct_1(F_33)
      | ~ m1_subset_1(E_32,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(E_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_350,plain,(
    ! [D_90,C_91,A_92,B_93] :
      ( D_90 = C_91
      | ~ r2_relset_1(A_92,B_93,C_91,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_356,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_350])).

tff(c_367,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_356])).

tff(c_596,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_618,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_596])).

tff(c_622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_618])).

tff(c_623,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_637,plain,(
    ! [E_140,B_144,A_141,D_143,C_142] :
      ( k1_xboole_0 = C_142
      | v2_funct_1(D_143)
      | ~ v2_funct_1(k1_partfun1(A_141,B_144,B_144,C_142,D_143,E_140))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(B_144,C_142)))
      | ~ v1_funct_2(E_140,B_144,C_142)
      | ~ v1_funct_1(E_140)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_144)))
      | ~ v1_funct_2(D_143,A_141,B_144)
      | ~ v1_funct_1(D_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_639,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_637])).

tff(c_641,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_67,c_639])).

tff(c_642,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_641])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_669,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_668,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_642,c_12])).

tff(c_158,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_171,plain,(
    ! [A_67] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_67,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_158])).

tff(c_180,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_759,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_180])).

tff(c_763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_759])).

tff(c_765,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_766,plain,(
    ! [A_153] : ~ r2_hidden(A_153,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_771,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_766])).

tff(c_110,plain,(
    ! [B_56,A_57] :
      ( ~ v1_xboole_0(B_56)
      | B_56 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_113,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_796,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_771,c_113])).

tff(c_834,plain,(
    ! [A_159] :
      ( A_159 = '#skF_5'
      | ~ v1_xboole_0(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_113])).

tff(c_844,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_765,c_834])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1147,plain,(
    ! [B_199,A_200] :
      ( B_199 = '#skF_5'
      | A_200 = '#skF_5'
      | k2_zfmisc_1(A_200,B_199) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_796,c_796,c_10])).

tff(c_1157,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_1147])).

tff(c_1162,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1157])).

tff(c_1184,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_771])).

tff(c_803,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_796,c_12])).

tff(c_1177,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_1162,c_803])).

tff(c_172,plain,(
    ! [A_67] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_67,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_158])).

tff(c_885,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_1314,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_885])).

tff(c_1318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_1314])).

tff(c_1319,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1157])).

tff(c_1342,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_771])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_802,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_5',B_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_796,c_14])).

tff(c_1340,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_2',B_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_1319,c_802])).

tff(c_1505,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1340,c_885])).

tff(c_1509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1342,c_1505])).

tff(c_1512,plain,(
    ! [A_229] : ~ r2_hidden(A_229,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_1517,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1512])).

tff(c_801,plain,(
    ! [A_57] :
      ( A_57 = '#skF_5'
      | ~ v1_xboole_0(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_113])).

tff(c_1523,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1517,c_801])).

tff(c_120,plain,(
    ! [A_59] : m1_subset_1(k6_partfun1(A_59),k1_zfmisc_1(k2_zfmisc_1(A_59,A_59))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_124,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_120])).

tff(c_160,plain,(
    ! [A_67] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_67,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_124,c_158])).

tff(c_174,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_160])).

tff(c_179,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_174])).

tff(c_810,plain,(
    v1_xboole_0(k6_partfun1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_179])).

tff(c_845,plain,(
    k6_partfun1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_810,c_834])).

tff(c_879,plain,(
    v2_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_845,c_67])).

tff(c_1525,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_879])).

tff(c_1540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1525])).

tff(c_1541,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1589,plain,(
    ! [C_240,A_241,B_242] :
      ( v1_relat_1(C_240)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1604,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1589])).

tff(c_1613,plain,(
    ! [C_245,B_246,A_247] :
      ( v5_relat_1(C_245,B_246)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_247,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1630,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1613])).

tff(c_1746,plain,(
    ! [A_264,B_265,D_266] :
      ( r2_relset_1(A_264,B_265,D_266,D_266)
      | ~ m1_subset_1(D_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1757,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_42,c_1746])).

tff(c_1802,plain,(
    ! [A_271,B_272,C_273] :
      ( k2_relset_1(A_271,B_272,C_273) = k2_relat_1(C_273)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1819,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1802])).

tff(c_2020,plain,(
    ! [E_309,D_313,F_308,B_312,C_311,A_310] :
      ( m1_subset_1(k1_partfun1(A_310,B_312,C_311,D_313,E_309,F_308),k1_zfmisc_1(k2_zfmisc_1(A_310,D_313)))
      | ~ m1_subset_1(F_308,k1_zfmisc_1(k2_zfmisc_1(C_311,D_313)))
      | ~ v1_funct_1(F_308)
      | ~ m1_subset_1(E_309,k1_zfmisc_1(k2_zfmisc_1(A_310,B_312)))
      | ~ v1_funct_1(E_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1866,plain,(
    ! [D_280,C_281,A_282,B_283] :
      ( D_280 = C_281
      | ~ r2_relset_1(A_282,B_283,C_281,D_280)
      | ~ m1_subset_1(D_280,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1876,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_54,c_1866])).

tff(c_1895,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1876])).

tff(c_1918,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1895])).

tff(c_2023,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2020,c_1918])).

tff(c_2054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_2023])).

tff(c_2055,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1895])).

tff(c_2511,plain,(
    ! [A_438,B_439,C_440,D_441] :
      ( k2_relset_1(A_438,B_439,C_440) = B_439
      | ~ r2_relset_1(B_439,B_439,k1_partfun1(B_439,A_438,A_438,B_439,D_441,C_440),k6_partfun1(B_439))
      | ~ m1_subset_1(D_441,k1_zfmisc_1(k2_zfmisc_1(B_439,A_438)))
      | ~ v1_funct_2(D_441,B_439,A_438)
      | ~ v1_funct_1(D_441)
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439)))
      | ~ v1_funct_2(C_440,A_438,B_439)
      | ~ v1_funct_1(C_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2514,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2055,c_2511])).

tff(c_2519,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_1757,c_1819,c_2514])).

tff(c_32,plain,(
    ! [B_27] :
      ( v2_funct_2(B_27,k2_relat_1(B_27))
      | ~ v5_relat_1(B_27,k2_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2525,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_32])).

tff(c_2529,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1604,c_1630,c_2519,c_2525])).

tff(c_2531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1541,c_2529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.89  
% 4.72/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.89  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.72/1.89  
% 4.72/1.89  %Foreground sorts:
% 4.72/1.89  
% 4.72/1.89  
% 4.72/1.89  %Background operators:
% 4.72/1.89  
% 4.72/1.89  
% 4.72/1.89  %Foreground operators:
% 4.72/1.89  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.72/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.72/1.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.72/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/1.89  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.72/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.72/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.72/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.72/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.72/1.89  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.72/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.72/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.72/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.72/1.89  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.72/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.72/1.89  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.72/1.89  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.72/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.72/1.89  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.72/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.72/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.72/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.72/1.89  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.72/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/1.89  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.72/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.72/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.72/1.89  
% 4.72/1.91  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 4.72/1.91  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.72/1.91  tff(f_103, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.72/1.91  tff(f_55, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 4.72/1.91  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.72/1.91  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.72/1.91  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.72/1.91  tff(f_142, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 4.72/1.91  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.72/1.91  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.72/1.91  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.72/1.91  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.72/1.91  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.72/1.91  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.72/1.91  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.72/1.91  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.72/1.91  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.72/1.91  tff(c_52, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.72/1.91  tff(c_94, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 4.72/1.91  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.72/1.91  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.72/1.91  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.72/1.91  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.72/1.91  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.72/1.91  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.72/1.91  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.72/1.91  tff(c_44, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.72/1.91  tff(c_18, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.72/1.91  tff(c_67, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 4.72/1.91  tff(c_36, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1(k1_partfun1(A_28, B_29, C_30, D_31, E_32, F_33), k1_zfmisc_1(k2_zfmisc_1(A_28, D_31))) | ~m1_subset_1(F_33, k1_zfmisc_1(k2_zfmisc_1(C_30, D_31))) | ~v1_funct_1(F_33) | ~m1_subset_1(E_32, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(E_32))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.72/1.91  tff(c_42, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.72/1.91  tff(c_54, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.72/1.91  tff(c_350, plain, (![D_90, C_91, A_92, B_93]: (D_90=C_91 | ~r2_relset_1(A_92, B_93, C_91, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.72/1.91  tff(c_356, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_350])).
% 4.72/1.91  tff(c_367, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_356])).
% 4.72/1.91  tff(c_596, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_367])).
% 4.72/1.91  tff(c_618, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_596])).
% 4.72/1.91  tff(c_622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_618])).
% 4.72/1.91  tff(c_623, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_367])).
% 4.72/1.91  tff(c_637, plain, (![E_140, B_144, A_141, D_143, C_142]: (k1_xboole_0=C_142 | v2_funct_1(D_143) | ~v2_funct_1(k1_partfun1(A_141, B_144, B_144, C_142, D_143, E_140)) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(B_144, C_142))) | ~v1_funct_2(E_140, B_144, C_142) | ~v1_funct_1(E_140) | ~m1_subset_1(D_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_144))) | ~v1_funct_2(D_143, A_141, B_144) | ~v1_funct_1(D_143))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.72/1.91  tff(c_639, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_623, c_637])).
% 4.72/1.91  tff(c_641, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_67, c_639])).
% 4.72/1.91  tff(c_642, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_94, c_641])).
% 4.72/1.91  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.72/1.91  tff(c_669, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_6])).
% 4.72/1.91  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.72/1.91  tff(c_668, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_642, c_12])).
% 4.72/1.91  tff(c_158, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.72/1.91  tff(c_171, plain, (![A_67]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_67, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_158])).
% 4.72/1.91  tff(c_180, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_171])).
% 4.72/1.91  tff(c_759, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_668, c_180])).
% 4.72/1.91  tff(c_763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_669, c_759])).
% 4.72/1.91  tff(c_765, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_171])).
% 4.72/1.91  tff(c_766, plain, (![A_153]: (~r2_hidden(A_153, '#skF_5'))), inference(splitRight, [status(thm)], [c_171])).
% 4.72/1.91  tff(c_771, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_766])).
% 4.72/1.91  tff(c_110, plain, (![B_56, A_57]: (~v1_xboole_0(B_56) | B_56=A_57 | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.72/1.91  tff(c_113, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_6, c_110])).
% 4.72/1.91  tff(c_796, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_771, c_113])).
% 4.72/1.91  tff(c_834, plain, (![A_159]: (A_159='#skF_5' | ~v1_xboole_0(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_796, c_113])).
% 4.72/1.91  tff(c_844, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(resolution, [status(thm)], [c_765, c_834])).
% 4.72/1.91  tff(c_10, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.72/1.91  tff(c_1147, plain, (![B_199, A_200]: (B_199='#skF_5' | A_200='#skF_5' | k2_zfmisc_1(A_200, B_199)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_796, c_796, c_10])).
% 4.72/1.91  tff(c_1157, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_844, c_1147])).
% 4.72/1.91  tff(c_1162, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_1157])).
% 4.72/1.91  tff(c_1184, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_771])).
% 4.72/1.91  tff(c_803, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_796, c_12])).
% 4.72/1.91  tff(c_1177, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_1162, c_803])).
% 4.72/1.91  tff(c_172, plain, (![A_67]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_158])).
% 4.72/1.91  tff(c_885, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_172])).
% 4.72/1.91  tff(c_1314, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1177, c_885])).
% 4.72/1.91  tff(c_1318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1184, c_1314])).
% 4.72/1.91  tff(c_1319, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_1157])).
% 4.72/1.91  tff(c_1342, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_771])).
% 4.72/1.91  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.72/1.91  tff(c_802, plain, (![B_8]: (k2_zfmisc_1('#skF_5', B_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_796, c_796, c_14])).
% 4.72/1.91  tff(c_1340, plain, (![B_8]: (k2_zfmisc_1('#skF_2', B_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_1319, c_802])).
% 4.72/1.91  tff(c_1505, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1340, c_885])).
% 4.72/1.91  tff(c_1509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1342, c_1505])).
% 4.72/1.91  tff(c_1512, plain, (![A_229]: (~r2_hidden(A_229, '#skF_4'))), inference(splitRight, [status(thm)], [c_172])).
% 4.72/1.91  tff(c_1517, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1512])).
% 4.72/1.91  tff(c_801, plain, (![A_57]: (A_57='#skF_5' | ~v1_xboole_0(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_796, c_113])).
% 4.72/1.91  tff(c_1523, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1517, c_801])).
% 4.72/1.91  tff(c_120, plain, (![A_59]: (m1_subset_1(k6_partfun1(A_59), k1_zfmisc_1(k2_zfmisc_1(A_59, A_59))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.72/1.91  tff(c_124, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_120])).
% 4.72/1.91  tff(c_160, plain, (![A_67]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_67, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_124, c_158])).
% 4.72/1.91  tff(c_174, plain, (![A_69]: (~r2_hidden(A_69, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_160])).
% 4.72/1.91  tff(c_179, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_174])).
% 4.72/1.91  tff(c_810, plain, (v1_xboole_0(k6_partfun1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_796, c_179])).
% 4.72/1.91  tff(c_845, plain, (k6_partfun1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_810, c_834])).
% 4.72/1.91  tff(c_879, plain, (v2_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_845, c_67])).
% 4.72/1.91  tff(c_1525, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_879])).
% 4.72/1.91  tff(c_1540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_1525])).
% 4.72/1.91  tff(c_1541, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 4.72/1.91  tff(c_1589, plain, (![C_240, A_241, B_242]: (v1_relat_1(C_240) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.72/1.91  tff(c_1604, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_1589])).
% 4.72/1.91  tff(c_1613, plain, (![C_245, B_246, A_247]: (v5_relat_1(C_245, B_246) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_247, B_246))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.72/1.91  tff(c_1630, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_1613])).
% 4.72/1.91  tff(c_1746, plain, (![A_264, B_265, D_266]: (r2_relset_1(A_264, B_265, D_266, D_266) | ~m1_subset_1(D_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.72/1.91  tff(c_1757, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_42, c_1746])).
% 4.72/1.91  tff(c_1802, plain, (![A_271, B_272, C_273]: (k2_relset_1(A_271, B_272, C_273)=k2_relat_1(C_273) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.91  tff(c_1819, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_1802])).
% 4.72/1.91  tff(c_2020, plain, (![E_309, D_313, F_308, B_312, C_311, A_310]: (m1_subset_1(k1_partfun1(A_310, B_312, C_311, D_313, E_309, F_308), k1_zfmisc_1(k2_zfmisc_1(A_310, D_313))) | ~m1_subset_1(F_308, k1_zfmisc_1(k2_zfmisc_1(C_311, D_313))) | ~v1_funct_1(F_308) | ~m1_subset_1(E_309, k1_zfmisc_1(k2_zfmisc_1(A_310, B_312))) | ~v1_funct_1(E_309))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.72/1.91  tff(c_1866, plain, (![D_280, C_281, A_282, B_283]: (D_280=C_281 | ~r2_relset_1(A_282, B_283, C_281, D_280) | ~m1_subset_1(D_280, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.72/1.91  tff(c_1876, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_54, c_1866])).
% 4.72/1.91  tff(c_1895, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1876])).
% 4.72/1.91  tff(c_1918, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1895])).
% 4.72/1.91  tff(c_2023, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2020, c_1918])).
% 4.72/1.91  tff(c_2054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_2023])).
% 4.72/1.91  tff(c_2055, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1895])).
% 4.72/1.91  tff(c_2511, plain, (![A_438, B_439, C_440, D_441]: (k2_relset_1(A_438, B_439, C_440)=B_439 | ~r2_relset_1(B_439, B_439, k1_partfun1(B_439, A_438, A_438, B_439, D_441, C_440), k6_partfun1(B_439)) | ~m1_subset_1(D_441, k1_zfmisc_1(k2_zfmisc_1(B_439, A_438))) | ~v1_funct_2(D_441, B_439, A_438) | ~v1_funct_1(D_441) | ~m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))) | ~v1_funct_2(C_440, A_438, B_439) | ~v1_funct_1(C_440))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.72/1.91  tff(c_2514, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2055, c_2511])).
% 4.72/1.91  tff(c_2519, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_1757, c_1819, c_2514])).
% 4.72/1.91  tff(c_32, plain, (![B_27]: (v2_funct_2(B_27, k2_relat_1(B_27)) | ~v5_relat_1(B_27, k2_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.72/1.91  tff(c_2525, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2519, c_32])).
% 4.72/1.91  tff(c_2529, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1604, c_1630, c_2519, c_2525])).
% 4.72/1.91  tff(c_2531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1541, c_2529])).
% 4.72/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.91  
% 4.72/1.91  Inference rules
% 4.72/1.91  ----------------------
% 4.72/1.91  #Ref     : 0
% 4.72/1.91  #Sup     : 559
% 4.72/1.91  #Fact    : 0
% 4.72/1.91  #Define  : 0
% 4.72/1.91  #Split   : 20
% 4.72/1.91  #Chain   : 0
% 4.72/1.91  #Close   : 0
% 4.72/1.91  
% 4.72/1.91  Ordering : KBO
% 4.72/1.91  
% 4.72/1.91  Simplification rules
% 4.72/1.91  ----------------------
% 4.72/1.91  #Subsume      : 53
% 4.72/1.91  #Demod        : 489
% 4.72/1.91  #Tautology    : 193
% 4.72/1.91  #SimpNegUnit  : 3
% 4.72/1.91  #BackRed      : 124
% 4.72/1.91  
% 4.72/1.91  #Partial instantiations: 0
% 4.72/1.91  #Strategies tried      : 1
% 4.72/1.91  
% 4.72/1.91  Timing (in seconds)
% 4.72/1.91  ----------------------
% 5.12/1.92  Preprocessing        : 0.36
% 5.12/1.92  Parsing              : 0.19
% 5.12/1.92  CNF conversion       : 0.02
% 5.12/1.92  Main loop            : 0.76
% 5.12/1.92  Inferencing          : 0.26
% 5.12/1.92  Reduction            : 0.28
% 5.12/1.92  Demodulation         : 0.20
% 5.12/1.92  BG Simplification    : 0.03
% 5.12/1.92  Subsumption          : 0.13
% 5.12/1.92  Abstraction          : 0.03
% 5.12/1.92  MUC search           : 0.00
% 5.12/1.92  Cooper               : 0.00
% 5.12/1.92  Total                : 1.16
% 5.12/1.92  Index Insertion      : 0.00
% 5.12/1.92  Index Deletion       : 0.00
% 5.12/1.92  Index Matching       : 0.00
% 5.12/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
