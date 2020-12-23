%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:04 EST 2020

% Result     : Theorem 6.69s
% Output     : CNFRefutation 6.69s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 647 expanded)
%              Number of leaves         :   44 ( 237 expanded)
%              Depth                    :   14
%              Number of atoms          :  231 (1501 expanded)
%              Number of equality atoms :   57 ( 477 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
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

tff(f_109,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_87,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_148,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_126,axiom,(
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

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_129,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_48,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_20,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    ! [A_9] : k2_relat_1(k6_partfun1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20])).

tff(c_22,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_73,plain,(
    ! [A_10] : v1_relat_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_150,plain,(
    ! [A_57] :
      ( k2_relat_1(A_57) != k1_xboole_0
      | k1_xboole_0 = A_57
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_153,plain,(
    ! [A_10] :
      ( k2_relat_1(k6_partfun1(A_10)) != k1_xboole_0
      | k6_partfun1(A_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_73,c_150])).

tff(c_158,plain,(
    ! [A_58] :
      ( k1_xboole_0 != A_58
      | k6_partfun1(A_58) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_153])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_164,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_58])).

tff(c_208,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_24,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_44,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_71,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_483,plain,(
    ! [D_97,C_98,A_99,B_100] :
      ( D_97 = C_98
      | ~ r2_relset_1(A_99,B_100,C_98,D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_491,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_483])).

tff(c_506,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_491])).

tff(c_531,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_849,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_531])).

tff(c_853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_849])).

tff(c_854,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_1199,plain,(
    ! [A_191,D_195,C_194,B_193,E_192] :
      ( k1_xboole_0 = C_194
      | v2_funct_1(D_195)
      | ~ v2_funct_1(k1_partfun1(A_191,B_193,B_193,C_194,D_195,E_192))
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(B_193,C_194)))
      | ~ v1_funct_2(E_192,B_193,C_194)
      | ~ v1_funct_1(E_192)
      | ~ m1_subset_1(D_195,k1_zfmisc_1(k2_zfmisc_1(A_191,B_193)))
      | ~ v1_funct_2(D_195,A_191,B_193)
      | ~ v1_funct_1(D_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1201,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_1199])).

tff(c_1203,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_72,c_1201])).

tff(c_1205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_208,c_1203])).

tff(c_1207,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1216,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_2])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1215,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_1207,c_8])).

tff(c_1255,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_60])).

tff(c_1324,plain,(
    ! [B_204,A_205] :
      ( v1_xboole_0(B_204)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(A_205))
      | ~ v1_xboole_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1327,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1255,c_1324])).

tff(c_1339,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_1327])).

tff(c_130,plain,(
    ! [B_53,A_54] :
      ( ~ v1_xboole_0(B_53)
      | B_53 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_2,c_130])).

tff(c_1213,plain,(
    ! [A_54] :
      ( A_54 = '#skF_1'
      | ~ v1_xboole_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_133])).

tff(c_1352,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1339,c_1213])).

tff(c_177,plain,(
    ! [A_58] :
      ( v2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_72])).

tff(c_1225,plain,(
    ! [A_58] :
      ( v2_funct_1('#skF_1')
      | A_58 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_1207,c_177])).

tff(c_1226,plain,(
    ! [A_58] : A_58 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1225])).

tff(c_1228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1226,c_1207])).

tff(c_1229,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1225])).

tff(c_1371,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_1229])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1214,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_1207,c_10])).

tff(c_1238,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1214,c_66])).

tff(c_1330,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1238,c_1324])).

tff(c_1342,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_1330])).

tff(c_1359,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1342,c_1213])).

tff(c_1387,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_1359])).

tff(c_1389,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_129])).

tff(c_1398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1371,c_1389])).

tff(c_1399,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1549,plain,(
    ! [C_220,A_221,B_222] :
      ( v1_relat_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1565,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1549])).

tff(c_1631,plain,(
    ! [C_230,B_231,A_232] :
      ( v5_relat_1(C_230,B_231)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_232,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1648,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1631])).

tff(c_1682,plain,(
    ! [A_239,B_240,D_241] :
      ( r2_relset_1(A_239,B_240,D_241,D_241)
      | ~ m1_subset_1(D_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1693,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_71,c_1682])).

tff(c_1752,plain,(
    ! [A_249,B_250,C_251] :
      ( k2_relset_1(A_249,B_250,C_251) = k2_relat_1(C_251)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1770,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1752])).

tff(c_1792,plain,(
    ! [D_253,C_254,A_255,B_256] :
      ( D_253 = C_254
      | ~ r2_relset_1(A_255,B_256,C_254,D_253)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1798,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_1792])).

tff(c_1809,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1798])).

tff(c_2153,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1809])).

tff(c_2156,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_2153])).

tff(c_2160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_2156])).

tff(c_2161,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1809])).

tff(c_2230,plain,(
    ! [A_322,B_323,C_324,D_325] :
      ( k2_relset_1(A_322,B_323,C_324) = B_323
      | ~ r2_relset_1(B_323,B_323,k1_partfun1(B_323,A_322,A_322,B_323,D_325,C_324),k6_partfun1(B_323))
      | ~ m1_subset_1(D_325,k1_zfmisc_1(k2_zfmisc_1(B_323,A_322)))
      | ~ v1_funct_2(D_325,B_323,A_322)
      | ~ v1_funct_1(D_325)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_322,B_323)))
      | ~ v1_funct_2(C_324,A_322,B_323)
      | ~ v1_funct_1(C_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2233,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2161,c_2230])).

tff(c_2238,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_1693,c_1770,c_2233])).

tff(c_40,plain,(
    ! [B_26] :
      ( v2_funct_2(B_26,k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2244,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2238,c_40])).

tff(c_2248,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1565,c_1648,c_2238,c_2244])).

tff(c_2250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1399,c_2248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 11:51:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.69/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.69/2.63  
% 6.69/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.69/2.63  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.69/2.63  
% 6.69/2.63  %Foreground sorts:
% 6.69/2.63  
% 6.69/2.63  
% 6.69/2.63  %Background operators:
% 6.69/2.63  
% 6.69/2.63  
% 6.69/2.63  %Foreground operators:
% 6.69/2.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.69/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.69/2.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.69/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.69/2.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.69/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.69/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.69/2.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.69/2.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.69/2.63  tff('#skF_2', type, '#skF_2': $i).
% 6.69/2.63  tff('#skF_3', type, '#skF_3': $i).
% 6.69/2.63  tff('#skF_1', type, '#skF_1': $i).
% 6.69/2.63  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.69/2.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.69/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.69/2.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.69/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.69/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.69/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.69/2.63  tff('#skF_4', type, '#skF_4': $i).
% 6.69/2.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.69/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.69/2.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.69/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.69/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.69/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.69/2.63  
% 6.69/2.66  tff(f_168, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.69/2.66  tff(f_109, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.69/2.66  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.69/2.66  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.69/2.66  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.69/2.66  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.69/2.66  tff(f_87, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.69/2.66  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.69/2.66  tff(f_148, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.69/2.66  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.69/2.66  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.69/2.66  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.69/2.66  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.69/2.66  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.69/2.66  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.69/2.66  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.69/2.66  tff(f_126, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.69/2.66  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.69/2.66  tff(c_56, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.69/2.66  tff(c_129, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 6.69/2.66  tff(c_48, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.69/2.66  tff(c_20, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.69/2.66  tff(c_74, plain, (![A_9]: (k2_relat_1(k6_partfun1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20])).
% 6.69/2.66  tff(c_22, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.69/2.66  tff(c_73, plain, (![A_10]: (v1_relat_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 6.69/2.66  tff(c_150, plain, (![A_57]: (k2_relat_1(A_57)!=k1_xboole_0 | k1_xboole_0=A_57 | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.69/2.66  tff(c_153, plain, (![A_10]: (k2_relat_1(k6_partfun1(A_10))!=k1_xboole_0 | k6_partfun1(A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_73, c_150])).
% 6.69/2.66  tff(c_158, plain, (![A_58]: (k1_xboole_0!=A_58 | k6_partfun1(A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_153])).
% 6.69/2.66  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.69/2.66  tff(c_164, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_158, c_58])).
% 6.69/2.66  tff(c_208, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_164])).
% 6.69/2.66  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.69/2.66  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.69/2.66  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.69/2.66  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.69/2.66  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.69/2.66  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.69/2.66  tff(c_24, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.69/2.66  tff(c_72, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 6.69/2.66  tff(c_44, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.69/2.66  tff(c_38, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.69/2.66  tff(c_71, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38])).
% 6.69/2.66  tff(c_483, plain, (![D_97, C_98, A_99, B_100]: (D_97=C_98 | ~r2_relset_1(A_99, B_100, C_98, D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.69/2.66  tff(c_491, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_483])).
% 6.69/2.67  tff(c_506, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_491])).
% 6.69/2.67  tff(c_531, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_506])).
% 6.69/2.67  tff(c_849, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_531])).
% 6.69/2.67  tff(c_853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_849])).
% 6.69/2.67  tff(c_854, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_506])).
% 6.69/2.67  tff(c_1199, plain, (![A_191, D_195, C_194, B_193, E_192]: (k1_xboole_0=C_194 | v2_funct_1(D_195) | ~v2_funct_1(k1_partfun1(A_191, B_193, B_193, C_194, D_195, E_192)) | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(B_193, C_194))) | ~v1_funct_2(E_192, B_193, C_194) | ~v1_funct_1(E_192) | ~m1_subset_1(D_195, k1_zfmisc_1(k2_zfmisc_1(A_191, B_193))) | ~v1_funct_2(D_195, A_191, B_193) | ~v1_funct_1(D_195))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.69/2.67  tff(c_1201, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_854, c_1199])).
% 6.69/2.67  tff(c_1203, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_72, c_1201])).
% 6.69/2.67  tff(c_1205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_208, c_1203])).
% 6.69/2.67  tff(c_1207, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_164])).
% 6.69/2.67  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.69/2.67  tff(c_1216, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_2])).
% 6.69/2.67  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.69/2.67  tff(c_1215, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_1207, c_8])).
% 6.69/2.67  tff(c_1255, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_60])).
% 6.69/2.67  tff(c_1324, plain, (![B_204, A_205]: (v1_xboole_0(B_204) | ~m1_subset_1(B_204, k1_zfmisc_1(A_205)) | ~v1_xboole_0(A_205))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.69/2.67  tff(c_1327, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1255, c_1324])).
% 6.69/2.67  tff(c_1339, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1216, c_1327])).
% 6.69/2.67  tff(c_130, plain, (![B_53, A_54]: (~v1_xboole_0(B_53) | B_53=A_54 | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.69/2.67  tff(c_133, plain, (![A_54]: (k1_xboole_0=A_54 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_2, c_130])).
% 6.69/2.67  tff(c_1213, plain, (![A_54]: (A_54='#skF_1' | ~v1_xboole_0(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_133])).
% 6.69/2.67  tff(c_1352, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_1339, c_1213])).
% 6.69/2.67  tff(c_177, plain, (![A_58]: (v2_funct_1(k1_xboole_0) | k1_xboole_0!=A_58)), inference(superposition, [status(thm), theory('equality')], [c_158, c_72])).
% 6.69/2.67  tff(c_1225, plain, (![A_58]: (v2_funct_1('#skF_1') | A_58!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_1207, c_177])).
% 6.69/2.67  tff(c_1226, plain, (![A_58]: (A_58!='#skF_1')), inference(splitLeft, [status(thm)], [c_1225])).
% 6.69/2.67  tff(c_1228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1226, c_1207])).
% 6.69/2.67  tff(c_1229, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_1225])).
% 6.69/2.67  tff(c_1371, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_1229])).
% 6.69/2.67  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.69/2.67  tff(c_1214, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_1207, c_10])).
% 6.69/2.67  tff(c_1238, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1214, c_66])).
% 6.69/2.67  tff(c_1330, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1238, c_1324])).
% 6.69/2.67  tff(c_1342, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1216, c_1330])).
% 6.69/2.67  tff(c_1359, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_1342, c_1213])).
% 6.69/2.67  tff(c_1387, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_1359])).
% 6.69/2.67  tff(c_1389, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1387, c_129])).
% 6.69/2.67  tff(c_1398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1371, c_1389])).
% 6.69/2.67  tff(c_1399, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 6.69/2.67  tff(c_1549, plain, (![C_220, A_221, B_222]: (v1_relat_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.69/2.67  tff(c_1565, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1549])).
% 6.69/2.67  tff(c_1631, plain, (![C_230, B_231, A_232]: (v5_relat_1(C_230, B_231) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_232, B_231))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.69/2.67  tff(c_1648, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_1631])).
% 6.69/2.67  tff(c_1682, plain, (![A_239, B_240, D_241]: (r2_relset_1(A_239, B_240, D_241, D_241) | ~m1_subset_1(D_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.69/2.67  tff(c_1693, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_71, c_1682])).
% 6.69/2.67  tff(c_1752, plain, (![A_249, B_250, C_251]: (k2_relset_1(A_249, B_250, C_251)=k2_relat_1(C_251) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.69/2.67  tff(c_1770, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1752])).
% 6.69/2.67  tff(c_1792, plain, (![D_253, C_254, A_255, B_256]: (D_253=C_254 | ~r2_relset_1(A_255, B_256, C_254, D_253) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.69/2.67  tff(c_1798, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_1792])).
% 6.69/2.67  tff(c_1809, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1798])).
% 6.69/2.67  tff(c_2153, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1809])).
% 6.69/2.67  tff(c_2156, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_2153])).
% 6.69/2.67  tff(c_2160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_2156])).
% 6.69/2.67  tff(c_2161, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1809])).
% 6.69/2.67  tff(c_2230, plain, (![A_322, B_323, C_324, D_325]: (k2_relset_1(A_322, B_323, C_324)=B_323 | ~r2_relset_1(B_323, B_323, k1_partfun1(B_323, A_322, A_322, B_323, D_325, C_324), k6_partfun1(B_323)) | ~m1_subset_1(D_325, k1_zfmisc_1(k2_zfmisc_1(B_323, A_322))) | ~v1_funct_2(D_325, B_323, A_322) | ~v1_funct_1(D_325) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_322, B_323))) | ~v1_funct_2(C_324, A_322, B_323) | ~v1_funct_1(C_324))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.69/2.67  tff(c_2233, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2161, c_2230])).
% 6.69/2.67  tff(c_2238, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_1693, c_1770, c_2233])).
% 6.69/2.67  tff(c_40, plain, (![B_26]: (v2_funct_2(B_26, k2_relat_1(B_26)) | ~v5_relat_1(B_26, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.69/2.67  tff(c_2244, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2238, c_40])).
% 6.69/2.67  tff(c_2248, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1565, c_1648, c_2238, c_2244])).
% 6.69/2.67  tff(c_2250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1399, c_2248])).
% 6.69/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.69/2.67  
% 6.69/2.67  Inference rules
% 6.69/2.67  ----------------------
% 6.69/2.67  #Ref     : 6
% 6.69/2.67  #Sup     : 451
% 6.69/2.67  #Fact    : 0
% 6.69/2.67  #Define  : 0
% 6.69/2.67  #Split   : 28
% 6.69/2.67  #Chain   : 0
% 6.69/2.67  #Close   : 0
% 6.69/2.67  
% 6.69/2.67  Ordering : KBO
% 6.69/2.67  
% 6.69/2.67  Simplification rules
% 6.69/2.67  ----------------------
% 6.69/2.67  #Subsume      : 46
% 6.69/2.67  #Demod        : 302
% 6.69/2.67  #Tautology    : 206
% 6.69/2.67  #SimpNegUnit  : 27
% 6.69/2.67  #BackRed      : 51
% 6.69/2.67  
% 6.69/2.67  #Partial instantiations: 0
% 6.69/2.67  #Strategies tried      : 1
% 6.69/2.67  
% 6.69/2.67  Timing (in seconds)
% 6.69/2.67  ----------------------
% 6.69/2.67  Preprocessing        : 0.58
% 6.69/2.67  Parsing              : 0.30
% 6.69/2.67  CNF conversion       : 0.04
% 6.69/2.67  Main loop            : 1.21
% 6.69/2.67  Inferencing          : 0.43
% 6.69/2.67  Reduction            : 0.41
% 6.69/2.67  Demodulation         : 0.29
% 6.69/2.67  BG Simplification    : 0.05
% 6.69/2.67  Subsumption          : 0.20
% 6.69/2.67  Abstraction          : 0.05
% 6.69/2.67  MUC search           : 0.00
% 6.69/2.67  Cooper               : 0.00
% 6.69/2.67  Total                : 1.87
% 6.69/2.67  Index Insertion      : 0.00
% 6.69/2.67  Index Deletion       : 0.00
% 6.69/2.68  Index Matching       : 0.00
% 6.69/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
