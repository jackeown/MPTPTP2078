%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:37 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  257 (2540 expanded)
%              Number of leaves         :   40 ( 838 expanded)
%              Depth                    :   16
%              Number of atoms          :  459 (6693 expanded)
%              Number of equality atoms :  175 (1672 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_118,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_8226,plain,(
    ! [C_7056,A_7057,B_7058] :
      ( v1_relat_1(C_7056)
      | ~ m1_subset_1(C_7056,k1_zfmisc_1(k2_zfmisc_1(A_7057,B_7058))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8248,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_8226])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_72,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_70,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_8651,plain,(
    ! [A_7095,B_7096,C_7097] :
      ( k2_relset_1(A_7095,B_7096,C_7097) = k2_relat_1(C_7097)
      | ~ m1_subset_1(C_7097,k1_zfmisc_1(k2_zfmisc_1(A_7095,B_7096))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8667,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_8651])).

tff(c_8679,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8667])).

tff(c_30,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_137,plain,(
    ! [A_48] :
      ( v1_funct_1(k2_funct_1(A_48))
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_136,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_140,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_136])).

tff(c_143,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_140])).

tff(c_189,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_196,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_189])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_196])).

tff(c_206,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_245,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_260,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_278,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_260])).

tff(c_610,plain,(
    ! [A_110,B_111,C_112] :
      ( k2_relset_1(A_110,B_111,C_112) = k2_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_620,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_610])).

tff(c_630,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_620])).

tff(c_26,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_207,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_20,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) != k1_xboole_0
      | k1_xboole_0 = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_310,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_278,c_20])).

tff(c_435,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_631,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_435])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_571,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_590,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_571])).

tff(c_809,plain,(
    ! [B_128,A_129,C_130] :
      ( k1_xboole_0 = B_128
      | k1_relset_1(A_129,B_128,C_130) = A_129
      | ~ v1_funct_2(C_130,A_129,B_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_825,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_809])).

tff(c_843,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_590,c_825])).

tff(c_844,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_843])).

tff(c_521,plain,(
    ! [A_96] :
      ( k2_relat_1(k2_funct_1(A_96)) = k1_relat_1(A_96)
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_64,plain,(
    ! [A_28] :
      ( v1_funct_2(A_28,k1_relat_1(A_28),k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2416,plain,(
    ! [A_229] :
      ( v1_funct_2(k2_funct_1(A_229),k1_relat_1(k2_funct_1(A_229)),k1_relat_1(A_229))
      | ~ v1_funct_1(k2_funct_1(A_229))
      | ~ v1_relat_1(k2_funct_1(A_229))
      | ~ v2_funct_1(A_229)
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_64])).

tff(c_2428,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_2416])).

tff(c_2442,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_78,c_72,c_207,c_2428])).

tff(c_2443,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2442])).

tff(c_2446,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_2443])).

tff(c_2450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_78,c_2446])).

tff(c_2452,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2442])).

tff(c_28,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_655,plain,(
    ! [A_117] :
      ( m1_subset_1(A_117,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_117),k2_relat_1(A_117))))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4905,plain,(
    ! [A_6793] :
      ( m1_subset_1(k2_funct_1(A_6793),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_6793)),k1_relat_1(A_6793))))
      | ~ v1_funct_1(k2_funct_1(A_6793))
      | ~ v1_relat_1(k2_funct_1(A_6793))
      | ~ v2_funct_1(A_6793)
      | ~ v1_funct_1(A_6793)
      | ~ v1_relat_1(A_6793) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_655])).

tff(c_4938,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_4905])).

tff(c_4959,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_78,c_72,c_2452,c_207,c_4938])).

tff(c_4983,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4959])).

tff(c_4998,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_78,c_72,c_630,c_4983])).

tff(c_5000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_4998])).

tff(c_5001,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_5016,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_2])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5014,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_5001,c_10])).

tff(c_5002,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_5024,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5001,c_5002])).

tff(c_5338,plain,(
    ! [A_6821,B_6822,C_6823] :
      ( k2_relset_1(A_6821,B_6822,C_6823) = k2_relat_1(C_6823)
      | ~ m1_subset_1(C_6823,k1_zfmisc_1(k2_zfmisc_1(A_6821,B_6822))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5357,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_5338])).

tff(c_5362,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5024,c_70,c_5357])).

tff(c_279,plain,(
    ! [B_74,A_75] :
      ( v1_xboole_0(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_303,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_279])).

tff(c_322,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_5364,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5362,c_322])).

tff(c_5372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5016,c_5014,c_5364])).

tff(c_5373,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_5378,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5373,c_4])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5390,plain,(
    ! [A_2] : r1_tarski('#skF_4',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_6])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_22,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_82,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_38])).

tff(c_5508,plain,(
    ! [A_22] :
      ( v1_funct_2('#skF_4',A_22,'#skF_4')
      | A_22 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_5378,c_5378,c_5378,c_5378,c_82])).

tff(c_5509,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5508])).

tff(c_5512,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_5509])).

tff(c_5516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5390,c_5512])).

tff(c_5518,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5508])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_223,plain,(
    ! [A_63,B_64] : m1_subset_1('#skF_1'(A_63,B_64),k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_229,plain,(
    ! [B_4] : m1_subset_1('#skF_1'(k1_xboole_0,B_4),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_223])).

tff(c_285,plain,(
    ! [B_4] :
      ( v1_xboole_0('#skF_1'(k1_xboole_0,B_4))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_229,c_279])).

tff(c_317,plain,(
    ! [B_77] : v1_xboole_0('#skF_1'(k1_xboole_0,B_77)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_285])).

tff(c_321,plain,(
    ! [B_77] : '#skF_1'(k1_xboole_0,B_77) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_317,c_4])).

tff(c_5530,plain,(
    ! [B_77] : '#skF_1'('#skF_4',B_77) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_5378,c_321])).

tff(c_60,plain,(
    ! [A_25,B_26] : m1_subset_1('#skF_1'(A_25,B_26),k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7073,plain,(
    ! [A_6954,B_6955,C_6956] :
      ( k1_relset_1(A_6954,B_6955,C_6956) = k1_relat_1(C_6956)
      | ~ m1_subset_1(C_6956,k1_zfmisc_1(k2_zfmisc_1(A_6954,B_6955))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7209,plain,(
    ! [A_6973,B_6974] : k1_relset_1(A_6973,B_6974,'#skF_1'(A_6973,B_6974)) = k1_relat_1('#skF_1'(A_6973,B_6974)) ),
    inference(resolution,[status(thm)],[c_60,c_7073])).

tff(c_7218,plain,(
    ! [B_77] : k1_relat_1('#skF_1'('#skF_4',B_77)) = k1_relset_1('#skF_4',B_77,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5530,c_7209])).

tff(c_7224,plain,(
    ! [B_77] : k1_relset_1('#skF_4',B_77,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5530,c_7218])).

tff(c_50,plain,(
    ! [A_25,B_26] : v1_funct_2('#skF_1'(A_25,B_26),A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_80,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_7366,plain,(
    ! [B_6991,C_6992] :
      ( k1_relset_1('#skF_4',B_6991,C_6992) = '#skF_4'
      | ~ v1_funct_2(C_6992,'#skF_4',B_6991)
      | ~ m1_subset_1(C_6992,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_5378,c_5378,c_5378,c_80])).

tff(c_7374,plain,(
    ! [B_26] :
      ( k1_relset_1('#skF_4',B_26,'#skF_1'('#skF_4',B_26)) = '#skF_4'
      | ~ m1_subset_1('#skF_1'('#skF_4',B_26),k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_7366])).

tff(c_7383,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5518,c_5530,c_7224,c_5530,c_7374])).

tff(c_6980,plain,(
    ! [A_6947] :
      ( k2_relat_1(k2_funct_1(A_6947)) = k1_relat_1(A_6947)
      | ~ v2_funct_1(A_6947)
      | ~ v1_funct_1(A_6947)
      | ~ v1_relat_1(A_6947) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8121,plain,(
    ! [A_7051] :
      ( v1_funct_2(k2_funct_1(A_7051),k1_relat_1(k2_funct_1(A_7051)),k1_relat_1(A_7051))
      | ~ v1_funct_1(k2_funct_1(A_7051))
      | ~ v1_relat_1(k2_funct_1(A_7051))
      | ~ v2_funct_1(A_7051)
      | ~ v1_funct_1(A_7051)
      | ~ v1_relat_1(A_7051) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6980,c_64])).

tff(c_8127,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7383,c_8121])).

tff(c_8137,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_78,c_72,c_207,c_8127])).

tff(c_8138,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8137])).

tff(c_8141,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_8138])).

tff(c_8145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_78,c_8141])).

tff(c_8147,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8137])).

tff(c_5385,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) != '#skF_4'
      | A_10 = '#skF_4'
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_5378,c_20])).

tff(c_8154,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8147,c_5385])).

tff(c_8198,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8154])).

tff(c_8201,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8198])).

tff(c_8204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_78,c_72,c_7383,c_8201])).

tff(c_8205,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8154])).

tff(c_5387,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_5378,c_12])).

tff(c_5924,plain,(
    ! [A_6869,B_6870,C_6871] :
      ( k1_relset_1(A_6869,B_6870,C_6871) = k1_relat_1(C_6871)
      | ~ m1_subset_1(C_6871,k1_zfmisc_1(k2_zfmisc_1(A_6869,B_6870))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5958,plain,(
    ! [A_6874,B_6875] : k1_relset_1(A_6874,B_6875,'#skF_1'(A_6874,B_6875)) = k1_relat_1('#skF_1'(A_6874,B_6875)) ),
    inference(resolution,[status(thm)],[c_60,c_5924])).

tff(c_5967,plain,(
    ! [B_77] : k1_relat_1('#skF_1'('#skF_4',B_77)) = k1_relset_1('#skF_4',B_77,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5530,c_5958])).

tff(c_5973,plain,(
    ! [B_77] : k1_relset_1('#skF_4',B_77,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5530,c_5967])).

tff(c_6051,plain,(
    ! [B_6887,C_6888] :
      ( k1_relset_1('#skF_4',B_6887,C_6888) = '#skF_4'
      | ~ v1_funct_2(C_6888,'#skF_4',B_6887)
      | ~ m1_subset_1(C_6888,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_5378,c_5378,c_5378,c_80])).

tff(c_6059,plain,(
    ! [B_26] :
      ( k1_relset_1('#skF_4',B_26,'#skF_1'('#skF_4',B_26)) = '#skF_4'
      | ~ m1_subset_1('#skF_1'('#skF_4',B_26),k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_6051])).

tff(c_6068,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5518,c_5530,c_5973,c_5530,c_6059])).

tff(c_214,plain,(
    ! [A_62] :
      ( v1_relat_1(k2_funct_1(A_62))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_221,plain,(
    ! [A_62] :
      ( k2_relat_1(k2_funct_1(A_62)) != k1_xboole_0
      | k2_funct_1(A_62) = k1_xboole_0
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_214,c_20])).

tff(c_6486,plain,(
    ! [A_6921] :
      ( k2_relat_1(k2_funct_1(A_6921)) != '#skF_4'
      | k2_funct_1(A_6921) = '#skF_4'
      | ~ v1_funct_1(A_6921)
      | ~ v1_relat_1(A_6921) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_5378,c_221])).

tff(c_6950,plain,(
    ! [A_6945] :
      ( k1_relat_1(A_6945) != '#skF_4'
      | k2_funct_1(A_6945) = '#skF_4'
      | ~ v1_funct_1(A_6945)
      | ~ v1_relat_1(A_6945)
      | ~ v2_funct_1(A_6945)
      | ~ v1_funct_1(A_6945)
      | ~ v1_relat_1(A_6945) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6486])).

tff(c_6953,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_6950])).

tff(c_6956,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_78,c_6068,c_6953])).

tff(c_5389,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_5378,c_10])).

tff(c_5374,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_5452,plain,(
    ! [A_6831] :
      ( A_6831 = '#skF_4'
      | ~ v1_xboole_0(A_6831) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_4])).

tff(c_5467,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5374,c_5452])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5399,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_4'
      | A_3 = '#skF_4'
      | k2_zfmisc_1(A_3,B_4) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5378,c_5378,c_5378,c_8])).

tff(c_5593,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5467,c_5399])).

tff(c_5600,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5593])).

tff(c_5603,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5600,c_245])).

tff(c_5608,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5389,c_5603])).

tff(c_6958,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6956,c_5608])).

tff(c_6964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5518,c_6958])).

tff(c_6965,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5593])).

tff(c_6969,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6965,c_245])).

tff(c_6974,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5387,c_6969])).

tff(c_8210,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8205,c_6974])).

tff(c_8218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5518,c_8210])).

tff(c_8219,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_8220,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_8680,plain,(
    ! [A_7098,B_7099,C_7100] :
      ( k1_relset_1(A_7098,B_7099,C_7100) = k1_relat_1(C_7100)
      | ~ m1_subset_1(C_7100,k1_zfmisc_1(k2_zfmisc_1(A_7098,B_7099))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8704,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8220,c_8680])).

tff(c_8892,plain,(
    ! [B_7114,C_7115,A_7116] :
      ( k1_xboole_0 = B_7114
      | v1_funct_2(C_7115,A_7116,B_7114)
      | k1_relset_1(A_7116,B_7114,C_7115) != A_7116
      | ~ m1_subset_1(C_7115,k1_zfmisc_1(k2_zfmisc_1(A_7116,B_7114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8901,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_8220,c_8892])).

tff(c_8924,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8704,c_8901])).

tff(c_8925,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_8219,c_8924])).

tff(c_8948,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8925])).

tff(c_8951,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8948])).

tff(c_8954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8248,c_78,c_72,c_8679,c_8951])).

tff(c_8955,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8925])).

tff(c_22,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) != k1_xboole_0
      | k1_xboole_0 = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8256,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8248,c_22])).

tff(c_8266,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8256])).

tff(c_8984,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8955,c_8266])).

tff(c_8255,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8248,c_20])).

tff(c_8265,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8255])).

tff(c_8708,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8679,c_8265])).

tff(c_8966,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8955,c_8708])).

tff(c_8707,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_8680])).

tff(c_48,plain,(
    ! [B_23,A_22,C_24] :
      ( k1_xboole_0 = B_23
      | k1_relset_1(A_22,B_23,C_24) = A_22
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_9067,plain,(
    ! [B_7123,A_7124,C_7125] :
      ( B_7123 = '#skF_2'
      | k1_relset_1(A_7124,B_7123,C_7125) = A_7124
      | ~ v1_funct_2(C_7125,A_7124,B_7123)
      | ~ m1_subset_1(C_7125,k1_zfmisc_1(k2_zfmisc_1(A_7124,B_7123))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8955,c_48])).

tff(c_9086,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_9067])).

tff(c_9099,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8707,c_9086])).

tff(c_9101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8984,c_8966,c_9099])).

tff(c_9102,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8256])).

tff(c_9104,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9102,c_8265])).

tff(c_9103,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8256])).

tff(c_9120,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9102,c_9103])).

tff(c_9439,plain,(
    ! [A_7156] :
      ( k2_relat_1(k2_funct_1(A_7156)) = k1_relat_1(A_7156)
      | ~ v2_funct_1(A_7156)
      | ~ v1_funct_1(A_7156)
      | ~ v1_relat_1(A_7156) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8244,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8220,c_8226])).

tff(c_8263,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8244,c_20])).

tff(c_9381,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9102,c_9102,c_8263])).

tff(c_9382,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9381])).

tff(c_9445,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9439,c_9382])).

tff(c_9455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8248,c_78,c_72,c_9120,c_9445])).

tff(c_9456,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9381])).

tff(c_8264,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8244,c_22])).

tff(c_9297,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9102,c_9102,c_8264])).

tff(c_9298,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9297])).

tff(c_9458,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9456,c_9298])).

tff(c_9466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9120,c_9458])).

tff(c_9467,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9297])).

tff(c_9594,plain,(
    ! [A_7164] :
      ( k1_relat_1(k2_funct_1(A_7164)) = k2_relat_1(A_7164)
      | ~ v2_funct_1(A_7164)
      | ~ v1_funct_1(A_7164)
      | ~ v1_relat_1(A_7164) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9606,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9467,c_9594])).

tff(c_9610,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8248,c_78,c_72,c_9120,c_9606])).

tff(c_9612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9104,c_9610])).

tff(c_9613,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8255])).

tff(c_9625,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9613,c_2])).

tff(c_9618,plain,(
    ! [B_4] : m1_subset_1('#skF_1'('#skF_4',B_4),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9613,c_9613,c_229])).

tff(c_9726,plain,(
    ! [B_7176,A_7177] :
      ( v1_xboole_0(B_7176)
      | ~ m1_subset_1(B_7176,k1_zfmisc_1(A_7177))
      | ~ v1_xboole_0(A_7177) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9729,plain,(
    ! [B_4] :
      ( v1_xboole_0('#skF_1'('#skF_4',B_4))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9618,c_9726])).

tff(c_9750,plain,(
    ! [B_7178] : v1_xboole_0('#skF_1'('#skF_4',B_7178)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9625,c_9729])).

tff(c_9622,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9613,c_4])).

tff(c_9760,plain,(
    ! [B_7179] : '#skF_1'('#skF_4',B_7179) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9750,c_9622])).

tff(c_9771,plain,(
    ! [B_7179] : v1_funct_2('#skF_4','#skF_4',B_7179) ),
    inference(superposition,[status(thm),theory(equality)],[c_9760,c_50])).

tff(c_9614,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8255])).

tff(c_9630,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9613,c_9614])).

tff(c_10316,plain,(
    ! [A_7226,B_7227,C_7228] :
      ( k2_relset_1(A_7226,B_7227,C_7228) = k2_relat_1(C_7228)
      | ~ m1_subset_1(C_7228,k1_zfmisc_1(k2_zfmisc_1(A_7226,B_7227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10338,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_10316])).

tff(c_10345,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9630,c_10338])).

tff(c_10018,plain,(
    ! [A_7201] :
      ( k1_relat_1(k2_funct_1(A_7201)) = k2_relat_1(A_7201)
      | ~ v2_funct_1(A_7201)
      | ~ v1_funct_1(A_7201)
      | ~ v1_relat_1(A_7201) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9884,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9613,c_9613,c_8264])).

tff(c_9885,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9884])).

tff(c_10027,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10018,c_9885])).

tff(c_10034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8248,c_78,c_72,c_9630,c_10027])).

tff(c_10035,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9884])).

tff(c_10040,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10035,c_8219])).

tff(c_10347,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10345,c_10040])).

tff(c_10355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9771,c_10347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.12/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.28/2.52  
% 7.28/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.28/2.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.28/2.52  
% 7.28/2.52  %Foreground sorts:
% 7.28/2.52  
% 7.28/2.52  
% 7.28/2.52  %Background operators:
% 7.28/2.52  
% 7.28/2.52  
% 7.28/2.52  %Foreground operators:
% 7.28/2.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.28/2.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.28/2.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.28/2.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.28/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.28/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.28/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.28/2.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.28/2.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.28/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.28/2.52  tff('#skF_3', type, '#skF_3': $i).
% 7.28/2.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.28/2.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.28/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.28/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.28/2.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.28/2.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.28/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.28/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.28/2.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.28/2.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.28/2.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.28/2.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.28/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.28/2.52  
% 7.49/2.55  tff(f_145, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 7.49/2.55  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.49/2.55  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.49/2.55  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.49/2.55  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.49/2.55  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.49/2.55  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.49/2.55  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.49/2.55  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.49/2.55  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.49/2.55  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.49/2.55  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 7.49/2.55  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.49/2.55  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.49/2.55  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.49/2.55  tff(f_118, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 7.49/2.55  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.49/2.55  tff(c_8226, plain, (![C_7056, A_7057, B_7058]: (v1_relat_1(C_7056) | ~m1_subset_1(C_7056, k1_zfmisc_1(k2_zfmisc_1(A_7057, B_7058))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.49/2.55  tff(c_8248, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_8226])).
% 7.49/2.55  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.49/2.55  tff(c_72, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.49/2.55  tff(c_70, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.49/2.55  tff(c_8651, plain, (![A_7095, B_7096, C_7097]: (k2_relset_1(A_7095, B_7096, C_7097)=k2_relat_1(C_7097) | ~m1_subset_1(C_7097, k1_zfmisc_1(k2_zfmisc_1(A_7095, B_7096))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.49/2.55  tff(c_8667, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_8651])).
% 7.49/2.55  tff(c_8679, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_8667])).
% 7.49/2.55  tff(c_30, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.49/2.55  tff(c_137, plain, (![A_48]: (v1_funct_1(k2_funct_1(A_48)) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.49/2.55  tff(c_68, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.49/2.55  tff(c_136, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 7.49/2.55  tff(c_140, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_137, c_136])).
% 7.49/2.55  tff(c_143, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_140])).
% 7.49/2.55  tff(c_189, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.49/2.55  tff(c_196, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_189])).
% 7.49/2.55  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_196])).
% 7.49/2.55  tff(c_206, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_68])).
% 7.49/2.55  tff(c_245, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_206])).
% 7.49/2.55  tff(c_260, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.49/2.55  tff(c_278, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_260])).
% 7.49/2.55  tff(c_610, plain, (![A_110, B_111, C_112]: (k2_relset_1(A_110, B_111, C_112)=k2_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.49/2.55  tff(c_620, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_610])).
% 7.49/2.55  tff(c_630, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_620])).
% 7.49/2.55  tff(c_26, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.49/2.55  tff(c_207, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 7.49/2.55  tff(c_20, plain, (![A_10]: (k2_relat_1(A_10)!=k1_xboole_0 | k1_xboole_0=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.49/2.55  tff(c_310, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_278, c_20])).
% 7.49/2.55  tff(c_435, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_310])).
% 7.49/2.55  tff(c_631, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_630, c_435])).
% 7.49/2.55  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.49/2.55  tff(c_571, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.49/2.55  tff(c_590, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_571])).
% 7.49/2.55  tff(c_809, plain, (![B_128, A_129, C_130]: (k1_xboole_0=B_128 | k1_relset_1(A_129, B_128, C_130)=A_129 | ~v1_funct_2(C_130, A_129, B_128) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.49/2.55  tff(c_825, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_809])).
% 7.49/2.55  tff(c_843, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_590, c_825])).
% 7.49/2.55  tff(c_844, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_631, c_843])).
% 7.49/2.55  tff(c_521, plain, (![A_96]: (k2_relat_1(k2_funct_1(A_96))=k1_relat_1(A_96) | ~v2_funct_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.49/2.55  tff(c_64, plain, (![A_28]: (v1_funct_2(A_28, k1_relat_1(A_28), k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.49/2.55  tff(c_2416, plain, (![A_229]: (v1_funct_2(k2_funct_1(A_229), k1_relat_1(k2_funct_1(A_229)), k1_relat_1(A_229)) | ~v1_funct_1(k2_funct_1(A_229)) | ~v1_relat_1(k2_funct_1(A_229)) | ~v2_funct_1(A_229) | ~v1_funct_1(A_229) | ~v1_relat_1(A_229))), inference(superposition, [status(thm), theory('equality')], [c_521, c_64])).
% 7.49/2.55  tff(c_2428, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_844, c_2416])).
% 7.49/2.55  tff(c_2442, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_78, c_72, c_207, c_2428])).
% 7.49/2.55  tff(c_2443, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2442])).
% 7.49/2.55  tff(c_2446, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_2443])).
% 7.49/2.55  tff(c_2450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_78, c_2446])).
% 7.49/2.55  tff(c_2452, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2442])).
% 7.49/2.55  tff(c_28, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.49/2.55  tff(c_655, plain, (![A_117]: (m1_subset_1(A_117, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_117), k2_relat_1(A_117)))) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.49/2.55  tff(c_4905, plain, (![A_6793]: (m1_subset_1(k2_funct_1(A_6793), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_6793)), k1_relat_1(A_6793)))) | ~v1_funct_1(k2_funct_1(A_6793)) | ~v1_relat_1(k2_funct_1(A_6793)) | ~v2_funct_1(A_6793) | ~v1_funct_1(A_6793) | ~v1_relat_1(A_6793))), inference(superposition, [status(thm), theory('equality')], [c_28, c_655])).
% 7.49/2.55  tff(c_4938, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_844, c_4905])).
% 7.49/2.55  tff(c_4959, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_78, c_72, c_2452, c_207, c_4938])).
% 7.49/2.55  tff(c_4983, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_4959])).
% 7.49/2.55  tff(c_4998, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_78, c_72, c_630, c_4983])).
% 7.49/2.55  tff(c_5000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_245, c_4998])).
% 7.49/2.55  tff(c_5001, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_310])).
% 7.49/2.55  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.49/2.55  tff(c_5016, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_2])).
% 7.49/2.55  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.49/2.55  tff(c_5014, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_5001, c_10])).
% 7.49/2.55  tff(c_5002, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_310])).
% 7.49/2.55  tff(c_5024, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5001, c_5002])).
% 7.49/2.55  tff(c_5338, plain, (![A_6821, B_6822, C_6823]: (k2_relset_1(A_6821, B_6822, C_6823)=k2_relat_1(C_6823) | ~m1_subset_1(C_6823, k1_zfmisc_1(k2_zfmisc_1(A_6821, B_6822))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.49/2.55  tff(c_5357, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_5338])).
% 7.49/2.55  tff(c_5362, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5024, c_70, c_5357])).
% 7.49/2.55  tff(c_279, plain, (![B_74, A_75]: (v1_xboole_0(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.49/2.55  tff(c_303, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_279])).
% 7.49/2.55  tff(c_322, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_303])).
% 7.49/2.55  tff(c_5364, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5362, c_322])).
% 7.49/2.55  tff(c_5372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5016, c_5014, c_5364])).
% 7.49/2.55  tff(c_5373, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_303])).
% 7.49/2.55  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.49/2.55  tff(c_5378, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5373, c_4])).
% 7.49/2.55  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.49/2.55  tff(c_5390, plain, (![A_2]: (r1_tarski('#skF_4', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_6])).
% 7.49/2.55  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.49/2.55  tff(c_38, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_22, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.49/2.55  tff(c_82, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_38])).
% 7.49/2.55  tff(c_5508, plain, (![A_22]: (v1_funct_2('#skF_4', A_22, '#skF_4') | A_22='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_5378, c_5378, c_5378, c_5378, c_82])).
% 7.49/2.55  tff(c_5509, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5508])).
% 7.49/2.55  tff(c_5512, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_5509])).
% 7.49/2.55  tff(c_5516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5390, c_5512])).
% 7.49/2.55  tff(c_5518, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5508])).
% 7.49/2.55  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.49/2.55  tff(c_223, plain, (![A_63, B_64]: (m1_subset_1('#skF_1'(A_63, B_64), k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.49/2.55  tff(c_229, plain, (![B_4]: (m1_subset_1('#skF_1'(k1_xboole_0, B_4), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_223])).
% 7.49/2.55  tff(c_285, plain, (![B_4]: (v1_xboole_0('#skF_1'(k1_xboole_0, B_4)) | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_229, c_279])).
% 7.49/2.55  tff(c_317, plain, (![B_77]: (v1_xboole_0('#skF_1'(k1_xboole_0, B_77)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_285])).
% 7.49/2.55  tff(c_321, plain, (![B_77]: ('#skF_1'(k1_xboole_0, B_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_317, c_4])).
% 7.49/2.55  tff(c_5530, plain, (![B_77]: ('#skF_1'('#skF_4', B_77)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_5378, c_321])).
% 7.49/2.56  tff(c_60, plain, (![A_25, B_26]: (m1_subset_1('#skF_1'(A_25, B_26), k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.49/2.56  tff(c_7073, plain, (![A_6954, B_6955, C_6956]: (k1_relset_1(A_6954, B_6955, C_6956)=k1_relat_1(C_6956) | ~m1_subset_1(C_6956, k1_zfmisc_1(k2_zfmisc_1(A_6954, B_6955))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.49/2.56  tff(c_7209, plain, (![A_6973, B_6974]: (k1_relset_1(A_6973, B_6974, '#skF_1'(A_6973, B_6974))=k1_relat_1('#skF_1'(A_6973, B_6974)))), inference(resolution, [status(thm)], [c_60, c_7073])).
% 7.49/2.56  tff(c_7218, plain, (![B_77]: (k1_relat_1('#skF_1'('#skF_4', B_77))=k1_relset_1('#skF_4', B_77, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5530, c_7209])).
% 7.49/2.56  tff(c_7224, plain, (![B_77]: (k1_relset_1('#skF_4', B_77, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5530, c_7218])).
% 7.49/2.56  tff(c_50, plain, (![A_25, B_26]: (v1_funct_2('#skF_1'(A_25, B_26), A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.49/2.56  tff(c_46, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.49/2.56  tff(c_80, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 7.49/2.56  tff(c_7366, plain, (![B_6991, C_6992]: (k1_relset_1('#skF_4', B_6991, C_6992)='#skF_4' | ~v1_funct_2(C_6992, '#skF_4', B_6991) | ~m1_subset_1(C_6992, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_5378, c_5378, c_5378, c_80])).
% 7.49/2.56  tff(c_7374, plain, (![B_26]: (k1_relset_1('#skF_4', B_26, '#skF_1'('#skF_4', B_26))='#skF_4' | ~m1_subset_1('#skF_1'('#skF_4', B_26), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_7366])).
% 7.49/2.56  tff(c_7383, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5518, c_5530, c_7224, c_5530, c_7374])).
% 7.49/2.56  tff(c_6980, plain, (![A_6947]: (k2_relat_1(k2_funct_1(A_6947))=k1_relat_1(A_6947) | ~v2_funct_1(A_6947) | ~v1_funct_1(A_6947) | ~v1_relat_1(A_6947))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.49/2.56  tff(c_8121, plain, (![A_7051]: (v1_funct_2(k2_funct_1(A_7051), k1_relat_1(k2_funct_1(A_7051)), k1_relat_1(A_7051)) | ~v1_funct_1(k2_funct_1(A_7051)) | ~v1_relat_1(k2_funct_1(A_7051)) | ~v2_funct_1(A_7051) | ~v1_funct_1(A_7051) | ~v1_relat_1(A_7051))), inference(superposition, [status(thm), theory('equality')], [c_6980, c_64])).
% 7.49/2.56  tff(c_8127, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7383, c_8121])).
% 7.49/2.56  tff(c_8137, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_78, c_72, c_207, c_8127])).
% 7.49/2.56  tff(c_8138, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8137])).
% 7.49/2.56  tff(c_8141, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_8138])).
% 7.49/2.56  tff(c_8145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_78, c_8141])).
% 7.49/2.56  tff(c_8147, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8137])).
% 7.49/2.56  tff(c_5385, plain, (![A_10]: (k2_relat_1(A_10)!='#skF_4' | A_10='#skF_4' | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_5378, c_20])).
% 7.49/2.56  tff(c_8154, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_8147, c_5385])).
% 7.49/2.56  tff(c_8198, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_8154])).
% 7.49/2.56  tff(c_8201, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_8198])).
% 7.49/2.56  tff(c_8204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_78, c_72, c_7383, c_8201])).
% 7.49/2.56  tff(c_8205, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_8154])).
% 7.49/2.56  tff(c_5387, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_5378, c_12])).
% 7.49/2.56  tff(c_5924, plain, (![A_6869, B_6870, C_6871]: (k1_relset_1(A_6869, B_6870, C_6871)=k1_relat_1(C_6871) | ~m1_subset_1(C_6871, k1_zfmisc_1(k2_zfmisc_1(A_6869, B_6870))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.49/2.56  tff(c_5958, plain, (![A_6874, B_6875]: (k1_relset_1(A_6874, B_6875, '#skF_1'(A_6874, B_6875))=k1_relat_1('#skF_1'(A_6874, B_6875)))), inference(resolution, [status(thm)], [c_60, c_5924])).
% 7.49/2.56  tff(c_5967, plain, (![B_77]: (k1_relat_1('#skF_1'('#skF_4', B_77))=k1_relset_1('#skF_4', B_77, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5530, c_5958])).
% 7.49/2.56  tff(c_5973, plain, (![B_77]: (k1_relset_1('#skF_4', B_77, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5530, c_5967])).
% 7.49/2.56  tff(c_6051, plain, (![B_6887, C_6888]: (k1_relset_1('#skF_4', B_6887, C_6888)='#skF_4' | ~v1_funct_2(C_6888, '#skF_4', B_6887) | ~m1_subset_1(C_6888, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_5378, c_5378, c_5378, c_80])).
% 7.49/2.56  tff(c_6059, plain, (![B_26]: (k1_relset_1('#skF_4', B_26, '#skF_1'('#skF_4', B_26))='#skF_4' | ~m1_subset_1('#skF_1'('#skF_4', B_26), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_6051])).
% 7.49/2.56  tff(c_6068, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5518, c_5530, c_5973, c_5530, c_6059])).
% 7.49/2.56  tff(c_214, plain, (![A_62]: (v1_relat_1(k2_funct_1(A_62)) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.49/2.56  tff(c_221, plain, (![A_62]: (k2_relat_1(k2_funct_1(A_62))!=k1_xboole_0 | k2_funct_1(A_62)=k1_xboole_0 | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_214, c_20])).
% 7.49/2.56  tff(c_6486, plain, (![A_6921]: (k2_relat_1(k2_funct_1(A_6921))!='#skF_4' | k2_funct_1(A_6921)='#skF_4' | ~v1_funct_1(A_6921) | ~v1_relat_1(A_6921))), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_5378, c_221])).
% 7.49/2.56  tff(c_6950, plain, (![A_6945]: (k1_relat_1(A_6945)!='#skF_4' | k2_funct_1(A_6945)='#skF_4' | ~v1_funct_1(A_6945) | ~v1_relat_1(A_6945) | ~v2_funct_1(A_6945) | ~v1_funct_1(A_6945) | ~v1_relat_1(A_6945))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6486])).
% 7.49/2.56  tff(c_6953, plain, (k1_relat_1('#skF_4')!='#skF_4' | k2_funct_1('#skF_4')='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_6950])).
% 7.49/2.56  tff(c_6956, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_278, c_78, c_6068, c_6953])).
% 7.49/2.56  tff(c_5389, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_5378, c_10])).
% 7.49/2.56  tff(c_5374, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_303])).
% 7.49/2.56  tff(c_5452, plain, (![A_6831]: (A_6831='#skF_4' | ~v1_xboole_0(A_6831))), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_4])).
% 7.49/2.56  tff(c_5467, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_5374, c_5452])).
% 7.49/2.56  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.49/2.56  tff(c_5399, plain, (![B_4, A_3]: (B_4='#skF_4' | A_3='#skF_4' | k2_zfmisc_1(A_3, B_4)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5378, c_5378, c_5378, c_8])).
% 7.49/2.56  tff(c_5593, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5467, c_5399])).
% 7.49/2.56  tff(c_5600, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_5593])).
% 7.49/2.56  tff(c_5603, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5600, c_245])).
% 7.49/2.56  tff(c_5608, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5389, c_5603])).
% 7.49/2.56  tff(c_6958, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6956, c_5608])).
% 7.49/2.56  tff(c_6964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5518, c_6958])).
% 7.49/2.56  tff(c_6965, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_5593])).
% 7.49/2.56  tff(c_6969, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6965, c_245])).
% 7.49/2.56  tff(c_6974, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5387, c_6969])).
% 7.49/2.56  tff(c_8210, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8205, c_6974])).
% 7.49/2.56  tff(c_8218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5518, c_8210])).
% 7.49/2.56  tff(c_8219, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_206])).
% 7.49/2.56  tff(c_8220, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_206])).
% 7.49/2.56  tff(c_8680, plain, (![A_7098, B_7099, C_7100]: (k1_relset_1(A_7098, B_7099, C_7100)=k1_relat_1(C_7100) | ~m1_subset_1(C_7100, k1_zfmisc_1(k2_zfmisc_1(A_7098, B_7099))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.49/2.56  tff(c_8704, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8220, c_8680])).
% 7.49/2.56  tff(c_8892, plain, (![B_7114, C_7115, A_7116]: (k1_xboole_0=B_7114 | v1_funct_2(C_7115, A_7116, B_7114) | k1_relset_1(A_7116, B_7114, C_7115)!=A_7116 | ~m1_subset_1(C_7115, k1_zfmisc_1(k2_zfmisc_1(A_7116, B_7114))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.49/2.56  tff(c_8901, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_8220, c_8892])).
% 7.49/2.56  tff(c_8924, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8704, c_8901])).
% 7.49/2.56  tff(c_8925, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_8219, c_8924])).
% 7.49/2.56  tff(c_8948, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_8925])).
% 7.49/2.56  tff(c_8951, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_8948])).
% 7.49/2.56  tff(c_8954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8248, c_78, c_72, c_8679, c_8951])).
% 7.49/2.56  tff(c_8955, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_8925])).
% 7.49/2.56  tff(c_22, plain, (![A_10]: (k1_relat_1(A_10)!=k1_xboole_0 | k1_xboole_0=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.49/2.56  tff(c_8256, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8248, c_22])).
% 7.49/2.56  tff(c_8266, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8256])).
% 7.49/2.56  tff(c_8984, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8955, c_8266])).
% 7.49/2.56  tff(c_8255, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8248, c_20])).
% 7.49/2.56  tff(c_8265, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8255])).
% 7.49/2.56  tff(c_8708, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8679, c_8265])).
% 7.49/2.56  tff(c_8966, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8955, c_8708])).
% 7.49/2.56  tff(c_8707, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_8680])).
% 7.49/2.56  tff(c_48, plain, (![B_23, A_22, C_24]: (k1_xboole_0=B_23 | k1_relset_1(A_22, B_23, C_24)=A_22 | ~v1_funct_2(C_24, A_22, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.49/2.56  tff(c_9067, plain, (![B_7123, A_7124, C_7125]: (B_7123='#skF_2' | k1_relset_1(A_7124, B_7123, C_7125)=A_7124 | ~v1_funct_2(C_7125, A_7124, B_7123) | ~m1_subset_1(C_7125, k1_zfmisc_1(k2_zfmisc_1(A_7124, B_7123))))), inference(demodulation, [status(thm), theory('equality')], [c_8955, c_48])).
% 7.49/2.56  tff(c_9086, plain, ('#skF_2'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_9067])).
% 7.49/2.56  tff(c_9099, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8707, c_9086])).
% 7.49/2.56  tff(c_9101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8984, c_8966, c_9099])).
% 7.49/2.56  tff(c_9102, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_8256])).
% 7.49/2.56  tff(c_9104, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9102, c_8265])).
% 7.49/2.56  tff(c_9103, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8256])).
% 7.49/2.56  tff(c_9120, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9102, c_9103])).
% 7.49/2.56  tff(c_9439, plain, (![A_7156]: (k2_relat_1(k2_funct_1(A_7156))=k1_relat_1(A_7156) | ~v2_funct_1(A_7156) | ~v1_funct_1(A_7156) | ~v1_relat_1(A_7156))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.49/2.56  tff(c_8244, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8220, c_8226])).
% 7.49/2.56  tff(c_8263, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0 | k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8244, c_20])).
% 7.49/2.56  tff(c_9381, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9102, c_9102, c_8263])).
% 7.49/2.56  tff(c_9382, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_9381])).
% 7.49/2.56  tff(c_9445, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9439, c_9382])).
% 7.49/2.56  tff(c_9455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8248, c_78, c_72, c_9120, c_9445])).
% 7.49/2.56  tff(c_9456, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_9381])).
% 7.49/2.56  tff(c_8264, plain, (k1_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0 | k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8244, c_22])).
% 7.49/2.56  tff(c_9297, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9102, c_9102, c_8264])).
% 7.49/2.56  tff(c_9298, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_9297])).
% 7.49/2.56  tff(c_9458, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9456, c_9298])).
% 7.49/2.56  tff(c_9466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9120, c_9458])).
% 7.49/2.56  tff(c_9467, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_9297])).
% 7.49/2.56  tff(c_9594, plain, (![A_7164]: (k1_relat_1(k2_funct_1(A_7164))=k2_relat_1(A_7164) | ~v2_funct_1(A_7164) | ~v1_funct_1(A_7164) | ~v1_relat_1(A_7164))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.49/2.56  tff(c_9606, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9467, c_9594])).
% 7.49/2.56  tff(c_9610, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8248, c_78, c_72, c_9120, c_9606])).
% 7.49/2.56  tff(c_9612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9104, c_9610])).
% 7.49/2.56  tff(c_9613, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_8255])).
% 7.49/2.56  tff(c_9625, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9613, c_2])).
% 7.49/2.56  tff(c_9618, plain, (![B_4]: (m1_subset_1('#skF_1'('#skF_4', B_4), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9613, c_9613, c_229])).
% 7.49/2.56  tff(c_9726, plain, (![B_7176, A_7177]: (v1_xboole_0(B_7176) | ~m1_subset_1(B_7176, k1_zfmisc_1(A_7177)) | ~v1_xboole_0(A_7177))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.49/2.56  tff(c_9729, plain, (![B_4]: (v1_xboole_0('#skF_1'('#skF_4', B_4)) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_9618, c_9726])).
% 7.49/2.56  tff(c_9750, plain, (![B_7178]: (v1_xboole_0('#skF_1'('#skF_4', B_7178)))), inference(demodulation, [status(thm), theory('equality')], [c_9625, c_9729])).
% 7.49/2.56  tff(c_9622, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_9613, c_4])).
% 7.49/2.56  tff(c_9760, plain, (![B_7179]: ('#skF_1'('#skF_4', B_7179)='#skF_4')), inference(resolution, [status(thm)], [c_9750, c_9622])).
% 7.49/2.56  tff(c_9771, plain, (![B_7179]: (v1_funct_2('#skF_4', '#skF_4', B_7179))), inference(superposition, [status(thm), theory('equality')], [c_9760, c_50])).
% 7.49/2.56  tff(c_9614, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8255])).
% 7.49/2.56  tff(c_9630, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9613, c_9614])).
% 7.49/2.56  tff(c_10316, plain, (![A_7226, B_7227, C_7228]: (k2_relset_1(A_7226, B_7227, C_7228)=k2_relat_1(C_7228) | ~m1_subset_1(C_7228, k1_zfmisc_1(k2_zfmisc_1(A_7226, B_7227))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.49/2.56  tff(c_10338, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_10316])).
% 7.49/2.56  tff(c_10345, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_9630, c_10338])).
% 7.49/2.56  tff(c_10018, plain, (![A_7201]: (k1_relat_1(k2_funct_1(A_7201))=k2_relat_1(A_7201) | ~v2_funct_1(A_7201) | ~v1_funct_1(A_7201) | ~v1_relat_1(A_7201))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.49/2.56  tff(c_9884, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9613, c_9613, c_8264])).
% 7.49/2.56  tff(c_9885, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_9884])).
% 7.49/2.56  tff(c_10027, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10018, c_9885])).
% 7.49/2.56  tff(c_10034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8248, c_78, c_72, c_9630, c_10027])).
% 7.49/2.56  tff(c_10035, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_9884])).
% 7.49/2.56  tff(c_10040, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10035, c_8219])).
% 7.49/2.56  tff(c_10347, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10345, c_10040])).
% 7.49/2.56  tff(c_10355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9771, c_10347])).
% 7.49/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.56  
% 7.49/2.56  Inference rules
% 7.49/2.56  ----------------------
% 7.49/2.56  #Ref     : 0
% 7.49/2.56  #Sup     : 1904
% 7.49/2.56  #Fact    : 12
% 7.49/2.56  #Define  : 0
% 7.49/2.56  #Split   : 32
% 7.49/2.56  #Chain   : 0
% 7.49/2.56  #Close   : 0
% 7.49/2.56  
% 7.49/2.56  Ordering : KBO
% 7.49/2.56  
% 7.49/2.56  Simplification rules
% 7.49/2.56  ----------------------
% 7.49/2.56  #Subsume      : 236
% 7.49/2.56  #Demod        : 2011
% 7.49/2.56  #Tautology    : 1163
% 7.49/2.56  #SimpNegUnit  : 15
% 7.49/2.56  #BackRed      : 191
% 7.49/2.56  
% 7.49/2.56  #Partial instantiations: 1395
% 7.49/2.56  #Strategies tried      : 1
% 7.49/2.56  
% 7.49/2.56  Timing (in seconds)
% 7.49/2.56  ----------------------
% 7.49/2.56  Preprocessing        : 0.35
% 7.49/2.56  Parsing              : 0.19
% 7.49/2.56  CNF conversion       : 0.02
% 7.49/2.56  Main loop            : 1.31
% 7.49/2.56  Inferencing          : 0.53
% 7.49/2.56  Reduction            : 0.43
% 7.49/2.56  Demodulation         : 0.31
% 7.49/2.56  BG Simplification    : 0.05
% 7.49/2.56  Subsumption          : 0.20
% 7.49/2.56  Abstraction          : 0.06
% 7.49/2.56  MUC search           : 0.00
% 7.49/2.56  Cooper               : 0.00
% 7.49/2.56  Total                : 1.75
% 7.49/2.56  Index Insertion      : 0.00
% 7.49/2.56  Index Deletion       : 0.00
% 7.49/2.56  Index Matching       : 0.00
% 7.49/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
