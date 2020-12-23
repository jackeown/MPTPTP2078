%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:01 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 269 expanded)
%              Number of leaves         :   45 ( 114 expanded)
%              Depth                    :    9
%              Number of atoms          :  217 ( 818 expanded)
%              Number of equality atoms :   25 (  62 expanded)
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

tff(f_172,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_113,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_91,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_152,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_130,axiom,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_114,plain,(
    ! [A_64] :
      ( v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64)
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_95,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_117,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_95])).

tff(c_120,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_117])).

tff(c_121,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(k2_zfmisc_1(A_5,B_6))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_136,plain,(
    ! [C_68,B_69,A_70] :
      ( ~ v1_xboole_0(C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    ! [A_70] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_70,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_136])).

tff(c_151,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_155,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_151])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_48,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_72,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_345,plain,(
    ! [C_115,E_119,F_117,D_120,A_118,B_116] :
      ( m1_subset_1(k1_partfun1(A_118,B_116,C_115,D_120,E_119,F_117),k1_zfmisc_1(k2_zfmisc_1(A_118,D_120)))
      | ~ m1_subset_1(F_117,k1_zfmisc_1(k2_zfmisc_1(C_115,D_120)))
      | ~ v1_funct_1(F_117)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_116)))
      | ~ v1_funct_1(E_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_71,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_58,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_270,plain,(
    ! [D_97,C_98,A_99,B_100] :
      ( D_97 = C_98
      | ~ r2_relset_1(A_99,B_100,C_98,D_97)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_278,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_58,c_270])).

tff(c_293,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_278])).

tff(c_294,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_354,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_345,c_294])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_354])).

tff(c_379,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_583,plain,(
    ! [E_178,A_177,D_175,B_176,C_179] :
      ( k1_xboole_0 = C_179
      | v2_funct_1(D_175)
      | ~ v2_funct_1(k1_partfun1(A_177,B_176,B_176,C_179,D_175,E_178))
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(B_176,C_179)))
      | ~ v1_funct_2(E_178,B_176,C_179)
      | ~ v1_funct_1(E_178)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(k2_zfmisc_1(A_177,B_176)))
      | ~ v1_funct_2(D_175,A_177,B_176)
      | ~ v1_funct_1(D_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_585,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_583])).

tff(c_590,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_72,c_585])).

tff(c_591,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_590])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_597,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_6])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_597])).

tff(c_602,plain,(
    ! [A_180] : ~ r2_hidden(A_180,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_606,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_602])).

tff(c_610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_606])).

tff(c_611,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_612,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_12,plain,(
    ! [A_10] :
      ( v1_relat_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_618,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_612,c_12])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_618])).

tff(c_625,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_645,plain,(
    ! [C_191,A_192,B_193] :
      ( v1_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_657,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_645])).

tff(c_660,plain,(
    ! [C_195,B_196,A_197] :
      ( v5_relat_1(C_195,B_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_671,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_660])).

tff(c_731,plain,(
    ! [A_213,B_214,D_215] :
      ( r2_relset_1(A_213,B_214,D_215,D_215)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_738,plain,(
    ! [A_27] : r2_relset_1(A_27,A_27,k6_partfun1(A_27),k6_partfun1(A_27)) ),
    inference(resolution,[status(thm)],[c_71,c_731])).

tff(c_763,plain,(
    ! [A_220,B_221,C_222] :
      ( k2_relset_1(A_220,B_221,C_222) = k2_relat_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_774,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_763])).

tff(c_850,plain,(
    ! [A_241,C_238,D_243,E_242,B_239,F_240] :
      ( m1_subset_1(k1_partfun1(A_241,B_239,C_238,D_243,E_242,F_240),k1_zfmisc_1(k2_zfmisc_1(A_241,D_243)))
      | ~ m1_subset_1(F_240,k1_zfmisc_1(k2_zfmisc_1(C_238,D_243)))
      | ~ v1_funct_1(F_240)
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_241,B_239)))
      | ~ v1_funct_1(E_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_780,plain,(
    ! [D_223,C_224,A_225,B_226] :
      ( D_223 = C_224
      | ~ r2_relset_1(A_225,B_226,C_224,D_223)
      | ~ m1_subset_1(D_223,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_788,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_58,c_780])).

tff(c_803,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_788])).

tff(c_817,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_803])).

tff(c_858,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_850,c_817])).

tff(c_880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_858])).

tff(c_881,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_803])).

tff(c_1148,plain,(
    ! [A_321,B_322,C_323,D_324] :
      ( k2_relset_1(A_321,B_322,C_323) = B_322
      | ~ r2_relset_1(B_322,B_322,k1_partfun1(B_322,A_321,A_321,B_322,D_324,C_323),k6_partfun1(B_322))
      | ~ m1_subset_1(D_324,k1_zfmisc_1(k2_zfmisc_1(B_322,A_321)))
      | ~ v1_funct_2(D_324,B_322,A_321)
      | ~ v1_funct_1(D_324)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322)))
      | ~ v1_funct_2(C_323,A_321,B_322)
      | ~ v1_funct_1(C_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1151,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_1148])).

tff(c_1153,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_738,c_774,c_1151])).

tff(c_40,plain,(
    ! [B_29] :
      ( v2_funct_2(B_29,k2_relat_1(B_29))
      | ~ v5_relat_1(B_29,k2_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1158,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_40])).

tff(c_1162,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_671,c_1153,c_1158])).

tff(c_1164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_625,c_1162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n016.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 10:38:34 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.88  
% 3.95/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.88  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.95/1.88  
% 3.95/1.88  %Foreground sorts:
% 3.95/1.88  
% 3.95/1.88  
% 3.95/1.88  %Background operators:
% 3.95/1.88  
% 3.95/1.88  
% 3.95/1.88  %Foreground operators:
% 3.95/1.88  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.95/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.95/1.88  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.95/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.88  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.95/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.95/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.88  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.95/1.88  tff('#skF_5', type, '#skF_5': $i).
% 3.95/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.95/1.88  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.88  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.88  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.95/1.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.95/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.88  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.95/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.88  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.88  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.95/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.95/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.95/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.88  
% 3.95/1.90  tff(f_172, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 3.95/1.90  tff(f_63, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.95/1.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.95/1.90  tff(f_36, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.95/1.90  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.95/1.90  tff(f_113, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.95/1.90  tff(f_67, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.95/1.90  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.95/1.90  tff(f_91, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.95/1.90  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.95/1.90  tff(f_152, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 3.95/1.90  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.95/1.90  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.95/1.90  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.95/1.90  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.95/1.90  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.95/1.90  tff(f_130, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.95/1.90  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 3.95/1.90  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.95/1.90  tff(c_114, plain, (![A_64]: (v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.95/1.90  tff(c_56, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.95/1.90  tff(c_95, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 3.95/1.90  tff(c_117, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_114, c_95])).
% 3.95/1.90  tff(c_120, plain, (~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_117])).
% 3.95/1.90  tff(c_121, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_120])).
% 3.95/1.90  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.90  tff(c_8, plain, (![A_5, B_6]: (v1_xboole_0(k2_zfmisc_1(A_5, B_6)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.95/1.90  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.95/1.90  tff(c_136, plain, (![C_68, B_69, A_70]: (~v1_xboole_0(C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.95/1.90  tff(c_145, plain, (![A_70]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_70, '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_136])).
% 3.95/1.90  tff(c_151, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_145])).
% 3.95/1.90  tff(c_155, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_151])).
% 3.95/1.90  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.95/1.90  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.95/1.90  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.95/1.90  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.95/1.90  tff(c_48, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.95/1.90  tff(c_24, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.95/1.90  tff(c_72, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 3.95/1.90  tff(c_345, plain, (![C_115, E_119, F_117, D_120, A_118, B_116]: (m1_subset_1(k1_partfun1(A_118, B_116, C_115, D_120, E_119, F_117), k1_zfmisc_1(k2_zfmisc_1(A_118, D_120))) | ~m1_subset_1(F_117, k1_zfmisc_1(k2_zfmisc_1(C_115, D_120))) | ~v1_funct_1(F_117) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_116))) | ~v1_funct_1(E_119))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.95/1.90  tff(c_38, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.95/1.90  tff(c_71, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38])).
% 3.95/1.90  tff(c_58, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.95/1.90  tff(c_270, plain, (![D_97, C_98, A_99, B_100]: (D_97=C_98 | ~r2_relset_1(A_99, B_100, C_98, D_97) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.95/1.90  tff(c_278, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_58, c_270])).
% 3.95/1.90  tff(c_293, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_278])).
% 3.95/1.90  tff(c_294, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_293])).
% 3.95/1.90  tff(c_354, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_345, c_294])).
% 3.95/1.90  tff(c_378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_354])).
% 3.95/1.90  tff(c_379, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_293])).
% 3.95/1.90  tff(c_583, plain, (![E_178, A_177, D_175, B_176, C_179]: (k1_xboole_0=C_179 | v2_funct_1(D_175) | ~v2_funct_1(k1_partfun1(A_177, B_176, B_176, C_179, D_175, E_178)) | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(B_176, C_179))) | ~v1_funct_2(E_178, B_176, C_179) | ~v1_funct_1(E_178) | ~m1_subset_1(D_175, k1_zfmisc_1(k2_zfmisc_1(A_177, B_176))) | ~v1_funct_2(D_175, A_177, B_176) | ~v1_funct_1(D_175))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.95/1.90  tff(c_585, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_379, c_583])).
% 3.95/1.90  tff(c_590, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_72, c_585])).
% 3.95/1.90  tff(c_591, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_95, c_590])).
% 3.95/1.90  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.95/1.90  tff(c_597, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_6])).
% 3.95/1.90  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_597])).
% 3.95/1.90  tff(c_602, plain, (![A_180]: (~r2_hidden(A_180, '#skF_4'))), inference(splitRight, [status(thm)], [c_145])).
% 3.95/1.90  tff(c_606, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_602])).
% 3.95/1.90  tff(c_610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_606])).
% 3.95/1.90  tff(c_611, plain, (~v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_120])).
% 3.95/1.90  tff(c_612, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_120])).
% 3.95/1.90  tff(c_12, plain, (![A_10]: (v1_relat_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.95/1.90  tff(c_618, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_612, c_12])).
% 3.95/1.90  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_611, c_618])).
% 3.95/1.90  tff(c_625, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 3.95/1.90  tff(c_645, plain, (![C_191, A_192, B_193]: (v1_relat_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.95/1.90  tff(c_657, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_645])).
% 3.95/1.90  tff(c_660, plain, (![C_195, B_196, A_197]: (v5_relat_1(C_195, B_196) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.95/1.90  tff(c_671, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_660])).
% 3.95/1.90  tff(c_731, plain, (![A_213, B_214, D_215]: (r2_relset_1(A_213, B_214, D_215, D_215) | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.95/1.90  tff(c_738, plain, (![A_27]: (r2_relset_1(A_27, A_27, k6_partfun1(A_27), k6_partfun1(A_27)))), inference(resolution, [status(thm)], [c_71, c_731])).
% 3.95/1.90  tff(c_763, plain, (![A_220, B_221, C_222]: (k2_relset_1(A_220, B_221, C_222)=k2_relat_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.95/1.90  tff(c_774, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_763])).
% 3.95/1.90  tff(c_850, plain, (![A_241, C_238, D_243, E_242, B_239, F_240]: (m1_subset_1(k1_partfun1(A_241, B_239, C_238, D_243, E_242, F_240), k1_zfmisc_1(k2_zfmisc_1(A_241, D_243))) | ~m1_subset_1(F_240, k1_zfmisc_1(k2_zfmisc_1(C_238, D_243))) | ~v1_funct_1(F_240) | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_241, B_239))) | ~v1_funct_1(E_242))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.95/1.90  tff(c_780, plain, (![D_223, C_224, A_225, B_226]: (D_223=C_224 | ~r2_relset_1(A_225, B_226, C_224, D_223) | ~m1_subset_1(D_223, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.95/1.90  tff(c_788, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_58, c_780])).
% 3.95/1.90  tff(c_803, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_788])).
% 3.95/1.90  tff(c_817, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_803])).
% 3.95/1.90  tff(c_858, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_850, c_817])).
% 3.95/1.90  tff(c_880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_858])).
% 3.95/1.90  tff(c_881, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_803])).
% 3.95/1.90  tff(c_1148, plain, (![A_321, B_322, C_323, D_324]: (k2_relset_1(A_321, B_322, C_323)=B_322 | ~r2_relset_1(B_322, B_322, k1_partfun1(B_322, A_321, A_321, B_322, D_324, C_323), k6_partfun1(B_322)) | ~m1_subset_1(D_324, k1_zfmisc_1(k2_zfmisc_1(B_322, A_321))) | ~v1_funct_2(D_324, B_322, A_321) | ~v1_funct_1(D_324) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))) | ~v1_funct_2(C_323, A_321, B_322) | ~v1_funct_1(C_323))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.95/1.90  tff(c_1151, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_881, c_1148])).
% 3.95/1.90  tff(c_1153, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_738, c_774, c_1151])).
% 3.95/1.90  tff(c_40, plain, (![B_29]: (v2_funct_2(B_29, k2_relat_1(B_29)) | ~v5_relat_1(B_29, k2_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.95/1.90  tff(c_1158, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1153, c_40])).
% 3.95/1.90  tff(c_1162, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_657, c_671, c_1153, c_1158])).
% 3.95/1.90  tff(c_1164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_625, c_1162])).
% 3.95/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.90  
% 3.95/1.90  Inference rules
% 3.95/1.90  ----------------------
% 3.95/1.90  #Ref     : 0
% 3.95/1.90  #Sup     : 226
% 3.95/1.90  #Fact    : 0
% 3.95/1.90  #Define  : 0
% 3.95/1.90  #Split   : 11
% 3.95/1.90  #Chain   : 0
% 3.95/1.90  #Close   : 0
% 3.95/1.90  
% 3.95/1.90  Ordering : KBO
% 3.95/1.90  
% 3.95/1.90  Simplification rules
% 3.95/1.90  ----------------------
% 3.95/1.90  #Subsume      : 1
% 3.95/1.90  #Demod        : 142
% 3.95/1.90  #Tautology    : 44
% 3.95/1.90  #SimpNegUnit  : 5
% 3.95/1.90  #BackRed      : 8
% 3.95/1.90  
% 3.95/1.90  #Partial instantiations: 0
% 3.95/1.90  #Strategies tried      : 1
% 3.95/1.90  
% 3.95/1.90  Timing (in seconds)
% 3.95/1.90  ----------------------
% 3.95/1.91  Preprocessing        : 0.56
% 3.95/1.91  Parsing              : 0.29
% 3.95/1.91  CNF conversion       : 0.04
% 3.95/1.91  Main loop            : 0.52
% 3.95/1.91  Inferencing          : 0.19
% 3.95/1.91  Reduction            : 0.16
% 3.95/1.91  Demodulation         : 0.12
% 3.95/1.91  BG Simplification    : 0.03
% 3.95/1.91  Subsumption          : 0.09
% 3.95/1.91  Abstraction          : 0.03
% 3.95/1.91  MUC search           : 0.00
% 3.95/1.91  Cooper               : 0.00
% 3.95/1.91  Total                : 1.12
% 3.95/1.91  Index Insertion      : 0.00
% 3.95/1.91  Index Deletion       : 0.00
% 3.95/1.91  Index Matching       : 0.00
% 3.95/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
