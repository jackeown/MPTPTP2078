%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:38 EST 2020

% Result     : Theorem 9.57s
% Output     : CNFRefutation 9.95s
% Verified   : 
% Statistics : Number of formulae       :  352 (2639 expanded)
%              Number of leaves         :   46 ( 827 expanded)
%              Depth                    :   18
%              Number of atoms          :  580 (7311 expanded)
%              Number of equality atoms :  196 (1057 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_131,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_15358,plain,(
    ! [A_1650,B_1651,C_1652,D_1653] :
      ( k2_partfun1(A_1650,B_1651,C_1652,D_1653) = k7_relat_1(C_1652,D_1653)
      | ~ m1_subset_1(C_1652,k1_zfmisc_1(k2_zfmisc_1(A_1650,B_1651)))
      | ~ v1_funct_1(C_1652) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_15367,plain,(
    ! [D_1653] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_1653) = k7_relat_1('#skF_5',D_1653)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_15358])).

tff(c_15379,plain,(
    ! [D_1653] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_1653) = k7_relat_1('#skF_5',D_1653) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_15367])).

tff(c_26,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_840,plain,(
    ! [B_146,A_147] :
      ( v1_relat_1(B_146)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_147))
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_846,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_840])).

tff(c_850,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_846])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12446,plain,(
    ! [A_1314,B_1315,C_1316,D_1317] :
      ( k7_relset_1(A_1314,B_1315,C_1316,D_1317) = k9_relat_1(C_1316,D_1317)
      | ~ m1_subset_1(C_1316,k1_zfmisc_1(k2_zfmisc_1(A_1314,B_1315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12458,plain,(
    ! [D_1318] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_1318) = k9_relat_1('#skF_5',D_1318) ),
    inference(resolution,[status(thm)],[c_70,c_12446])).

tff(c_9436,plain,(
    ! [A_1051,B_1052,C_1053,D_1054] :
      ( k2_partfun1(A_1051,B_1052,C_1053,D_1054) = k7_relat_1(C_1053,D_1054)
      | ~ m1_subset_1(C_1053,k1_zfmisc_1(k2_zfmisc_1(A_1051,B_1052)))
      | ~ v1_funct_1(C_1053) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_9443,plain,(
    ! [D_1054] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_1054) = k7_relat_1('#skF_5',D_1054)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_9436])).

tff(c_9454,plain,(
    ! [D_1054] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_1054) = k7_relat_1('#skF_5',D_1054) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9443])).

tff(c_68,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k7_relat_1(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7031,plain,(
    ! [C_799,A_800,B_801] :
      ( m1_subset_1(C_799,k1_zfmisc_1(k2_zfmisc_1(A_800,B_801)))
      | ~ r1_tarski(k2_relat_1(C_799),B_801)
      | ~ r1_tarski(k1_relat_1(C_799),A_800)
      | ~ v1_relat_1(C_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6913,plain,(
    ! [A_779,B_780,C_781,D_782] :
      ( k2_partfun1(A_779,B_780,C_781,D_782) = k7_relat_1(C_781,D_782)
      | ~ m1_subset_1(C_781,k1_zfmisc_1(k2_zfmisc_1(A_779,B_780)))
      | ~ v1_funct_1(C_781) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6918,plain,(
    ! [D_782] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_782) = k7_relat_1('#skF_5',D_782)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_6913])).

tff(c_6926,plain,(
    ! [D_782] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_782) = k7_relat_1('#skF_5',D_782) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6918])).

tff(c_796,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( v1_funct_1(k2_partfun1(A_139,B_140,C_141,D_142))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_801,plain,(
    ! [D_142] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_142))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_796])).

tff(c_809,plain,(
    ! [D_142] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_142)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_801])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_142,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_142])).

tff(c_813,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4535,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_813])).

tff(c_6929,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6926,c_4535])).

tff(c_7062,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7031,c_6929])).

tff(c_7113,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7062])).

tff(c_7116,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_7113])).

tff(c_7120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_7116])).

tff(c_7122,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7062])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_72,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4983,plain,(
    ! [A_601,B_602,C_603] :
      ( k1_relset_1(A_601,B_602,C_603) = k1_relat_1(C_603)
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_601,B_602))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4998,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_4983])).

tff(c_5513,plain,(
    ! [B_681,A_682,C_683] :
      ( k1_xboole_0 = B_681
      | k1_relset_1(A_682,B_681,C_683) = A_682
      | ~ v1_funct_2(C_683,A_682,B_681)
      | ~ m1_subset_1(C_683,k1_zfmisc_1(k2_zfmisc_1(A_682,B_681))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5523,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_5513])).

tff(c_5534,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4998,c_5523])).

tff(c_5536,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5534])).

tff(c_4497,plain,(
    ! [C_547,A_548,B_549] :
      ( v4_relat_1(C_547,A_548)
      | ~ m1_subset_1(C_547,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4512,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4497])).

tff(c_4633,plain,(
    ! [B_577,A_578] :
      ( k7_relat_1(B_577,A_578) = B_577
      | ~ v4_relat_1(B_577,A_578)
      | ~ v1_relat_1(B_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4645,plain,
    ( k7_relat_1('#skF_5','#skF_1') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4512,c_4633])).

tff(c_4655,plain,(
    k7_relat_1('#skF_5','#skF_1') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_4645])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_20,A_19)),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4691,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4655,c_32])).

tff(c_4700,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_4691])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4714,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4700,c_4])).

tff(c_4760,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4714])).

tff(c_5538,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5536,c_4760])).

tff(c_5542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5538])).

tff(c_5543,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5534])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_5584,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5543,c_2])).

tff(c_5586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5584])).

tff(c_5587,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4714])).

tff(c_5676,plain,(
    ! [B_690,A_691] :
      ( k1_relat_1(k7_relat_1(B_690,A_691)) = A_691
      | ~ r1_tarski(A_691,k1_relat_1(B_690))
      | ~ v1_relat_1(B_690) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5683,plain,(
    ! [A_691] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_691)) = A_691
      | ~ r1_tarski(A_691,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5587,c_5676])).

tff(c_5704,plain,(
    ! [A_691] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_691)) = A_691
      | ~ r1_tarski(A_691,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_5683])).

tff(c_5811,plain,(
    ! [B_701] :
      ( k1_relat_1(k7_relat_1(B_701,k1_relat_1(B_701))) = k1_relat_1(B_701)
      | ~ v1_relat_1(B_701) ) ),
    inference(resolution,[status(thm)],[c_8,c_5676])).

tff(c_6074,plain,(
    ! [A_717] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_5',A_717),A_717)) = k1_relat_1(k7_relat_1('#skF_5',A_717))
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_717))
      | ~ r1_tarski(A_717,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5704,c_5811])).

tff(c_6104,plain,(
    ! [A_717] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_5',A_717)),A_717)
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_717))
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_717))
      | ~ r1_tarski(A_717,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6074,c_32])).

tff(c_6862,plain,(
    ! [A_766,B_767,C_768,D_769] :
      ( k7_relset_1(A_766,B_767,C_768,D_769) = k9_relat_1(C_768,D_769)
      | ~ m1_subset_1(C_768,k1_zfmisc_1(k2_zfmisc_1(A_766,B_767))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6873,plain,(
    ! [D_769] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_769) = k9_relat_1('#skF_5',D_769) ),
    inference(resolution,[status(thm)],[c_70,c_6862])).

tff(c_66,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_6876,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6873,c_66])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7121,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_7062])).

tff(c_7140,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7121])).

tff(c_7143,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7140])).

tff(c_7146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_6876,c_7143])).

tff(c_7147,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_7121])).

tff(c_7193,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_6104,c_7147])).

tff(c_7203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_7122,c_7193])).

tff(c_7204,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_813])).

tff(c_9467,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9454,c_7204])).

tff(c_7704,plain,(
    ! [A_863,B_864,C_865] :
      ( k1_relset_1(A_863,B_864,C_865) = k1_relat_1(C_865)
      | ~ m1_subset_1(C_865,k1_zfmisc_1(k2_zfmisc_1(A_863,B_864))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7723,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_7704])).

tff(c_8393,plain,(
    ! [B_947,A_948,C_949] :
      ( k1_xboole_0 = B_947
      | k1_relset_1(A_948,B_947,C_949) = A_948
      | ~ v1_funct_2(C_949,A_948,B_947)
      | ~ m1_subset_1(C_949,k1_zfmisc_1(k2_zfmisc_1(A_948,B_947))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8406,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_8393])).

tff(c_8419,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7723,c_8406])).

tff(c_8421,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8419])).

tff(c_7239,plain,(
    ! [B_825,A_826] :
      ( k7_relat_1(B_825,A_826) = B_825
      | ~ v4_relat_1(B_825,A_826)
      | ~ v1_relat_1(B_825) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7245,plain,
    ( k7_relat_1('#skF_5','#skF_1') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4512,c_7239])).

tff(c_7249,plain,(
    k7_relat_1('#skF_5','#skF_1') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_7245])).

tff(c_7260,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7249,c_32])).

tff(c_7267,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_7260])).

tff(c_7305,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_7267,c_4])).

tff(c_7352,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7305])).

tff(c_8423,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8421,c_7352])).

tff(c_8427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8423])).

tff(c_8428,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8419])).

tff(c_8470,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8428,c_2])).

tff(c_8472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_8470])).

tff(c_8473,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7305])).

tff(c_8662,plain,(
    ! [B_961,A_962] :
      ( k1_relat_1(k7_relat_1(B_961,A_962)) = A_962
      | ~ r1_tarski(A_962,k1_relat_1(B_961))
      | ~ v1_relat_1(B_961) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8669,plain,(
    ! [A_962] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_962)) = A_962
      | ~ r1_tarski(A_962,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8473,c_8662])).

tff(c_8690,plain,(
    ! [A_962] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_962)) = A_962
      | ~ r1_tarski(A_962,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_8669])).

tff(c_7205,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_813])).

tff(c_22,plain,(
    ! [B_10,A_8] :
      ( v1_relat_1(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8483,plain,
    ( v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_7205,c_22])).

tff(c_8491,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8483])).

tff(c_9465,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9454,c_8491])).

tff(c_38,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8488,plain,(
    v4_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7205,c_38])).

tff(c_9463,plain,(
    v4_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9454,c_8488])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_9483,plain,
    ( k7_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_2') = k7_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_9463,c_30])).

tff(c_9486,plain,(
    k7_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_2') = k7_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9465,c_9483])).

tff(c_876,plain,(
    ! [B_150,A_151] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_150,A_151)),A_151)
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_888,plain,(
    ! [B_150,A_151] :
      ( k1_relat_1(k7_relat_1(B_150,A_151)) = A_151
      | ~ r1_tarski(A_151,k1_relat_1(k7_relat_1(B_150,A_151)))
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_876,c_4])).

tff(c_9602,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1(k7_relat_1('#skF_5','#skF_2')))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9486,c_888])).

tff(c_9618,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1(k7_relat_1('#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9465,c_9486,c_9602])).

tff(c_9698,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1(k7_relat_1('#skF_5','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_9618])).

tff(c_9702,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8690,c_9698])).

tff(c_9705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8,c_9702])).

tff(c_9706,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9618])).

tff(c_8882,plain,(
    ! [A_977,B_978,C_979] :
      ( k1_relset_1(A_977,B_978,C_979) = k1_relat_1(C_979)
      | ~ m1_subset_1(C_979,k1_zfmisc_1(k2_zfmisc_1(A_977,B_978))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8899,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7205,c_8882])).

tff(c_9460,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9454,c_9454,c_8899])).

tff(c_9708,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9706,c_9460])).

tff(c_9466,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9454,c_7205])).

tff(c_9843,plain,(
    ! [B_1069,C_1070,A_1071] :
      ( k1_xboole_0 = B_1069
      | v1_funct_2(C_1070,A_1071,B_1069)
      | k1_relset_1(A_1071,B_1069,C_1070) != A_1071
      | ~ m1_subset_1(C_1070,k1_zfmisc_1(k2_zfmisc_1(A_1071,B_1069))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_9846,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_9466,c_9843])).

tff(c_9865,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9708,c_9846])).

tff(c_9866,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_9467,c_9865])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9913,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9866,c_10])).

tff(c_9382,plain,(
    ! [A_1038,B_1039,C_1040,D_1041] :
      ( k7_relset_1(A_1038,B_1039,C_1040,D_1041) = k9_relat_1(C_1040,D_1041)
      | ~ m1_subset_1(C_1040,k1_zfmisc_1(k2_zfmisc_1(A_1038,B_1039))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_9396,plain,(
    ! [D_1041] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_1041) = k9_relat_1('#skF_5',D_1041) ),
    inference(resolution,[status(thm)],[c_70,c_9382])).

tff(c_123,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,
    ( k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_123])).

tff(c_4496,plain,(
    ~ r1_tarski('#skF_3',k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_9397,plain,(
    ~ r1_tarski('#skF_3',k9_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9396,c_4496])).

tff(c_9923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9913,c_9397])).

tff(c_9924,plain,(
    k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_12464,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12458,c_9924])).

tff(c_12880,plain,(
    ! [A_1373,B_1374,C_1375,D_1376] :
      ( k2_partfun1(A_1373,B_1374,C_1375,D_1376) = k7_relat_1(C_1375,D_1376)
      | ~ m1_subset_1(C_1375,k1_zfmisc_1(k2_zfmisc_1(A_1373,B_1374)))
      | ~ v1_funct_1(C_1375) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_12887,plain,(
    ! [D_1376] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_1376) = k7_relat_1('#skF_5',D_1376)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_12880])).

tff(c_12896,plain,(
    ! [D_1376] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_1376) = k7_relat_1('#skF_5',D_1376) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12887])).

tff(c_12756,plain,(
    ! [A_1358,B_1359,C_1360,D_1361] :
      ( k2_partfun1(A_1358,B_1359,C_1360,D_1361) = k7_relat_1(C_1360,D_1361)
      | ~ m1_subset_1(C_1360,k1_zfmisc_1(k2_zfmisc_1(A_1358,B_1359)))
      | ~ v1_funct_1(C_1360) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_12763,plain,(
    ! [D_1361] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_1361) = k7_relat_1('#skF_5',D_1361)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_12756])).

tff(c_12772,plain,(
    ! [D_1361] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_1361) = k7_relat_1('#skF_5',D_1361) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12763])).

tff(c_12559,plain,(
    ! [C_1334,A_1335,B_1336] :
      ( m1_subset_1(C_1334,k1_zfmisc_1(k2_zfmisc_1(A_1335,B_1336)))
      | ~ r1_tarski(k2_relat_1(C_1334),B_1336)
      | ~ r1_tarski(k1_relat_1(C_1334),A_1335)
      | ~ v1_relat_1(C_1334) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_9957,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_813])).

tff(c_12591,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12559,c_9957])).

tff(c_12663,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12591])).

tff(c_12828,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12772,c_12663])).

tff(c_12847,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_12828])).

tff(c_12851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_12847])).

tff(c_12853,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12591])).

tff(c_12897,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12896,c_12853])).

tff(c_10338,plain,(
    ! [A_1122,B_1123,C_1124] :
      ( k1_relset_1(A_1122,B_1123,C_1124) = k1_relat_1(C_1124)
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(k2_zfmisc_1(A_1122,B_1123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10353,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_10338])).

tff(c_10976,plain,(
    ! [B_1209,A_1210,C_1211] :
      ( k1_xboole_0 = B_1209
      | k1_relset_1(A_1210,B_1209,C_1211) = A_1210
      | ~ v1_funct_2(C_1211,A_1210,B_1209)
      | ~ m1_subset_1(C_1211,k1_zfmisc_1(k2_zfmisc_1(A_1210,B_1209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10986,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_10976])).

tff(c_10997,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_10353,c_10986])).

tff(c_10999,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10997])).

tff(c_9934,plain,(
    ! [C_1072,A_1073,B_1074] :
      ( v4_relat_1(C_1072,A_1073)
      | ~ m1_subset_1(C_1072,k1_zfmisc_1(k2_zfmisc_1(A_1073,B_1074))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9949,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_9934])).

tff(c_10010,plain,(
    ! [B_1089,A_1090] :
      ( k7_relat_1(B_1089,A_1090) = B_1089
      | ~ v4_relat_1(B_1089,A_1090)
      | ~ v1_relat_1(B_1089) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10022,plain,
    ( k7_relat_1('#skF_5','#skF_1') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9949,c_10010])).

tff(c_10032,plain,(
    k7_relat_1('#skF_5','#skF_1') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_10022])).

tff(c_10039,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10032,c_32])).

tff(c_10048,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_10039])).

tff(c_10091,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10048,c_4])).

tff(c_10130,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10091])).

tff(c_11001,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10999,c_10130])).

tff(c_11005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11001])).

tff(c_11006,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10997])).

tff(c_11047,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11006,c_2])).

tff(c_11049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_11047])).

tff(c_11050,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10091])).

tff(c_11126,plain,(
    ! [B_1219,A_1220] :
      ( k1_relat_1(k7_relat_1(B_1219,A_1220)) = A_1220
      | ~ r1_tarski(A_1220,k1_relat_1(B_1219))
      | ~ v1_relat_1(B_1219) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11129,plain,(
    ! [A_1220] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_1220)) = A_1220
      | ~ r1_tarski(A_1220,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11050,c_11126])).

tff(c_11149,plain,(
    ! [A_1220] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_1220)) = A_1220
      | ~ r1_tarski(A_1220,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_11129])).

tff(c_11313,plain,(
    ! [B_1236] :
      ( k1_relat_1(k7_relat_1(B_1236,k1_relat_1(B_1236))) = k1_relat_1(B_1236)
      | ~ v1_relat_1(B_1236) ) ),
    inference(resolution,[status(thm)],[c_8,c_11126])).

tff(c_11399,plain,(
    ! [A_1239] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_5',A_1239),A_1239)) = k1_relat_1(k7_relat_1('#skF_5',A_1239))
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_1239))
      | ~ r1_tarski(A_1239,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11149,c_11313])).

tff(c_11418,plain,(
    ! [A_1239] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_5',A_1239)),A_1239)
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_1239))
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_1239))
      | ~ r1_tarski(A_1239,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11399,c_32])).

tff(c_44,plain,(
    ! [C_35,A_33,B_34] :
      ( m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ r1_tarski(k2_relat_1(C_35),B_34)
      | ~ r1_tarski(k1_relat_1(C_35),A_33)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12900,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12896,c_9957])).

tff(c_12916,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_12900])).

tff(c_12922,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12897,c_12916])).

tff(c_12924,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_12922])).

tff(c_12927,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_11418,c_12924])).

tff(c_12937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_12897,c_12927])).

tff(c_12938,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_12922])).

tff(c_12977,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_12938])).

tff(c_12980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_8,c_12464,c_12977])).

tff(c_12981,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_813])).

tff(c_15392,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15379,c_12981])).

tff(c_13502,plain,(
    ! [A_1433,B_1434,C_1435] :
      ( k1_relset_1(A_1433,B_1434,C_1435) = k1_relat_1(C_1435)
      | ~ m1_subset_1(C_1435,k1_zfmisc_1(k2_zfmisc_1(A_1433,B_1434))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_13521,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_13502])).

tff(c_14161,plain,(
    ! [B_1528,A_1529,C_1530] :
      ( k1_xboole_0 = B_1528
      | k1_relset_1(A_1529,B_1528,C_1530) = A_1529
      | ~ v1_funct_2(C_1530,A_1529,B_1528)
      | ~ m1_subset_1(C_1530,k1_zfmisc_1(k2_zfmisc_1(A_1529,B_1528))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_14171,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_14161])).

tff(c_14182,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_13521,c_14171])).

tff(c_14184,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14182])).

tff(c_13042,plain,(
    ! [B_1395,A_1396] :
      ( k7_relat_1(B_1395,A_1396) = B_1395
      | ~ v4_relat_1(B_1395,A_1396)
      | ~ v1_relat_1(B_1395) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_13054,plain,
    ( k7_relat_1('#skF_5','#skF_1') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9949,c_13042])).

tff(c_13064,plain,(
    k7_relat_1('#skF_5','#skF_1') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_13054])).

tff(c_13068,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13064,c_32])).

tff(c_13075,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_13068])).

tff(c_13113,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_13075,c_4])).

tff(c_13175,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_13113])).

tff(c_14186,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14184,c_13175])).

tff(c_14190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14186])).

tff(c_14191,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14182])).

tff(c_14236,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14191,c_2])).

tff(c_14238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_14236])).

tff(c_14239,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13113])).

tff(c_14445,plain,(
    ! [B_1550,A_1551] :
      ( k1_relat_1(k7_relat_1(B_1550,A_1551)) = A_1551
      | ~ r1_tarski(A_1551,k1_relat_1(B_1550))
      | ~ v1_relat_1(B_1550) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14452,plain,(
    ! [A_1551] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_1551)) = A_1551
      | ~ r1_tarski(A_1551,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14239,c_14445])).

tff(c_14473,plain,(
    ! [A_1551] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_1551)) = A_1551
      | ~ r1_tarski(A_1551,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_14452])).

tff(c_15265,plain,(
    ! [A_1644,B_1645,C_1646,D_1647] :
      ( k2_partfun1(A_1644,B_1645,C_1646,D_1647) = k7_relat_1(C_1646,D_1647)
      | ~ m1_subset_1(C_1646,k1_zfmisc_1(k2_zfmisc_1(A_1644,B_1645)))
      | ~ v1_funct_1(C_1646) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_15274,plain,(
    ! [D_1647] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_1647) = k7_relat_1('#skF_5',D_1647)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_15265])).

tff(c_15286,plain,(
    ! [D_1647] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_1647) = k7_relat_1('#skF_5',D_1647) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_15274])).

tff(c_12982,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_813])).

tff(c_13159,plain,
    ( v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12982,c_22])).

tff(c_13167,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_13159])).

tff(c_13164,plain,(
    v4_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12982,c_38])).

tff(c_13171,plain,
    ( k7_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2') = k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_13164,c_30])).

tff(c_13174,plain,(
    k7_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2') = k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13167,c_13171])).

tff(c_15043,plain,(
    ! [B_1602,A_1603] :
      ( k1_relat_1(k7_relat_1(B_1602,A_1603)) = A_1603
      | ~ r1_tarski(A_1603,k1_relat_1(k7_relat_1(B_1602,A_1603)))
      | ~ v1_relat_1(B_1602) ) ),
    inference(resolution,[status(thm)],[c_876,c_4])).

tff(c_15046,plain,
    ( k1_relat_1(k7_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')))
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13174,c_15043])).

tff(c_15070,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13167,c_13174,c_15046])).

tff(c_15231,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_15070])).

tff(c_15287,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1(k7_relat_1('#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15286,c_15231])).

tff(c_15335,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14473,c_15287])).

tff(c_15338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8,c_15335])).

tff(c_15339,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_15070])).

tff(c_15380,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15379,c_15339])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_13168,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12982,c_18])).

tff(c_15387,plain,(
    r1_tarski(k7_relat_1('#skF_5','#skF_2'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15379,c_13168])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14827,plain,(
    ! [A_1575,B_1576,C_1577] :
      ( k1_relset_1(A_1575,B_1576,C_1577) = k1_relat_1(C_1577)
      | ~ m1_subset_1(C_1577,k1_zfmisc_1(k2_zfmisc_1(A_1575,B_1576))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14845,plain,(
    ! [A_1575,B_1576,A_6] :
      ( k1_relset_1(A_1575,B_1576,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_1575,B_1576)) ) ),
    inference(resolution,[status(thm)],[c_20,c_14827])).

tff(c_15456,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_15387,c_14845])).

tff(c_15469,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15380,c_15456])).

tff(c_15391,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15379,c_12982])).

tff(c_15616,plain,(
    ! [B_1660,C_1661,A_1662] :
      ( k1_xboole_0 = B_1660
      | v1_funct_2(C_1661,A_1662,B_1660)
      | k1_relset_1(A_1662,B_1660,C_1661) != A_1662
      | ~ m1_subset_1(C_1661,k1_zfmisc_1(k2_zfmisc_1(A_1662,B_1660))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_15619,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_15391,c_15616])).

tff(c_15638,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15469,c_15619])).

tff(c_15639,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_15392,c_15638])).

tff(c_15684,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15639,c_10])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15683,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15639,c_15639,c_14])).

tff(c_14254,plain,
    ( k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_13168,c_4])).

tff(c_14334,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_14254])).

tff(c_15386,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15379,c_14334])).

tff(c_15979,plain,(
    ~ r1_tarski('#skF_3',k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15683,c_15386])).

tff(c_15983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15684,c_15979])).

tff(c_15984,plain,(
    k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_14254])).

tff(c_15991,plain,(
    ~ v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15984,c_12981])).

tff(c_18382,plain,(
    ! [A_1854,B_1855,C_1856,D_1857] :
      ( k2_partfun1(A_1854,B_1855,C_1856,D_1857) = k7_relat_1(C_1856,D_1857)
      | ~ m1_subset_1(C_1856,k1_zfmisc_1(k2_zfmisc_1(A_1854,B_1855)))
      | ~ v1_funct_1(C_1856) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_18389,plain,(
    ! [D_1857] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_1857) = k7_relat_1('#skF_5',D_1857)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_18382])).

tff(c_18417,plain,(
    ! [D_1860] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_1860) = k7_relat_1('#skF_5',D_1860) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_18389])).

tff(c_18423,plain,(
    k7_relat_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18417,c_15984])).

tff(c_16022,plain,(
    ! [B_1674,A_1675] :
      ( k1_relat_1(k7_relat_1(B_1674,A_1675)) = A_1675
      | ~ r1_tarski(A_1675,k1_relat_1(B_1674))
      | ~ v1_relat_1(B_1674) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16025,plain,(
    ! [A_1675] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_1675)) = A_1675
      | ~ r1_tarski(A_1675,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14239,c_16022])).

tff(c_16045,plain,(
    ! [A_1675] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_1675)) = A_1675
      | ~ r1_tarski(A_1675,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_16025])).

tff(c_18453,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18423,c_16045])).

tff(c_18475,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_18453])).

tff(c_16468,plain,(
    ! [A_1709,B_1710,C_1711] :
      ( k1_relset_1(A_1709,B_1710,C_1711) = k1_relat_1(C_1711)
      | ~ m1_subset_1(C_1711,k1_zfmisc_1(k2_zfmisc_1(A_1709,B_1710))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16577,plain,(
    ! [A_1722,B_1723,A_1724] :
      ( k1_relset_1(A_1722,B_1723,A_1724) = k1_relat_1(A_1724)
      | ~ r1_tarski(A_1724,k2_zfmisc_1(A_1722,B_1723)) ) ),
    inference(resolution,[status(thm)],[c_20,c_16468])).

tff(c_16609,plain,(
    ! [A_1722,B_1723] : k1_relset_1(A_1722,B_1723,k2_zfmisc_1(A_1722,B_1723)) = k1_relat_1(k2_zfmisc_1(A_1722,B_1723)) ),
    inference(resolution,[status(thm)],[c_8,c_16577])).

tff(c_15990,plain,(
    m1_subset_1(k2_zfmisc_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15984,c_12982])).

tff(c_18754,plain,(
    ! [B_1885,C_1886,A_1887] :
      ( k1_xboole_0 = B_1885
      | v1_funct_2(C_1886,A_1887,B_1885)
      | k1_relset_1(A_1887,B_1885,C_1886) != A_1887
      | ~ m1_subset_1(C_1886,k1_zfmisc_1(k2_zfmisc_1(A_1887,B_1885))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_18760,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_15990,c_18754])).

tff(c_18777,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18475,c_16609,c_18760])).

tff(c_18778,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_15991,c_18777])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    ! [A_52,B_53] : v1_relat_1(k2_zfmisc_1(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_108,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_106])).

tff(c_12989,plain,(
    ! [A_1386,A_1387,B_1388] :
      ( v4_relat_1(A_1386,A_1387)
      | ~ r1_tarski(A_1386,k2_zfmisc_1(A_1387,B_1388)) ) ),
    inference(resolution,[status(thm)],[c_20,c_9934])).

tff(c_13014,plain,(
    ! [A_1387] : v4_relat_1(k1_xboole_0,A_1387) ),
    inference(resolution,[status(thm)],[c_10,c_12989])).

tff(c_13048,plain,(
    ! [A_1387] :
      ( k7_relat_1(k1_xboole_0,A_1387) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13014,c_13042])).

tff(c_13079,plain,(
    ! [A_1397] : k7_relat_1(k1_xboole_0,A_1397) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_13048])).

tff(c_137,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_123])).

tff(c_887,plain,(
    ! [B_150] :
      ( k1_relat_1(k7_relat_1(B_150,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_876,c_137])).

tff(c_13085,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13079,c_887])).

tff(c_13096,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_13085])).

tff(c_16598,plain,(
    ! [A_1722,B_1723] : k1_relset_1(A_1722,B_1723,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_16577])).

tff(c_16608,plain,(
    ! [A_1722,B_1723] : k1_relset_1(A_1722,B_1723,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13096,c_16598])).

tff(c_46,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_36,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_79,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_14304,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_14307,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_14304])).

tff(c_14311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14307])).

tff(c_14313,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_50,plain,(
    ! [C_38,B_37] :
      ( v1_funct_2(C_38,k1_xboole_0,B_37)
      | k1_relset_1(k1_xboole_0,B_37,C_38) != k1_xboole_0
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_16840,plain,(
    ! [C_1734,B_1735] :
      ( v1_funct_2(C_1734,k1_xboole_0,B_1735)
      | k1_relset_1(k1_xboole_0,B_1735,C_1734) != k1_xboole_0
      | ~ m1_subset_1(C_1734,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_16842,plain,(
    ! [B_1735] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_1735)
      | k1_relset_1(k1_xboole_0,B_1735,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14313,c_16840])).

tff(c_16848,plain,(
    ! [B_1735] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_1735) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16608,c_16842])).

tff(c_18800,plain,(
    ! [B_1735] : v1_funct_2('#skF_3','#skF_3',B_1735) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18778,c_18778,c_16848])).

tff(c_18821,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18778,c_18778,c_13096])).

tff(c_18831,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18778,c_18778,c_14])).

tff(c_19169,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18831,c_18475])).

tff(c_19184,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18821,c_19169])).

tff(c_19174,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18831,c_15991])).

tff(c_19437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18800,c_19184,c_19174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.57/3.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.83/3.78  
% 9.83/3.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.83/3.78  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.83/3.78  
% 9.83/3.78  %Foreground sorts:
% 9.83/3.78  
% 9.83/3.78  
% 9.83/3.78  %Background operators:
% 9.83/3.78  
% 9.83/3.78  
% 9.83/3.78  %Foreground operators:
% 9.83/3.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.83/3.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.83/3.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.83/3.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.83/3.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.83/3.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.83/3.78  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.83/3.78  tff('#skF_5', type, '#skF_5': $i).
% 9.83/3.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.83/3.78  tff('#skF_2', type, '#skF_2': $i).
% 9.83/3.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.83/3.78  tff('#skF_3', type, '#skF_3': $i).
% 9.83/3.78  tff('#skF_1', type, '#skF_1': $i).
% 9.83/3.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.83/3.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.83/3.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.83/3.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.83/3.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.83/3.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.83/3.78  tff('#skF_4', type, '#skF_4': $i).
% 9.83/3.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.83/3.78  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.83/3.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.83/3.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.83/3.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.83/3.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.83/3.78  
% 9.95/3.82  tff(f_152, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 9.95/3.82  tff(f_131, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.95/3.82  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.95/3.82  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.95/3.82  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.95/3.82  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.95/3.82  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.95/3.82  tff(f_99, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 9.95/3.82  tff(f_125, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.95/3.82  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.95/3.82  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.95/3.82  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.95/3.82  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 9.95/3.82  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 9.95/3.82  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.95/3.82  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 9.95/3.82  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 9.95/3.82  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.95/3.82  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.95/3.82  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.95/3.82  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.95/3.82  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.95/3.82  tff(c_15358, plain, (![A_1650, B_1651, C_1652, D_1653]: (k2_partfun1(A_1650, B_1651, C_1652, D_1653)=k7_relat_1(C_1652, D_1653) | ~m1_subset_1(C_1652, k1_zfmisc_1(k2_zfmisc_1(A_1650, B_1651))) | ~v1_funct_1(C_1652))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.95/3.82  tff(c_15367, plain, (![D_1653]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1653)=k7_relat_1('#skF_5', D_1653) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_15358])).
% 9.95/3.82  tff(c_15379, plain, (![D_1653]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1653)=k7_relat_1('#skF_5', D_1653))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_15367])).
% 9.95/3.82  tff(c_26, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.95/3.82  tff(c_840, plain, (![B_146, A_147]: (v1_relat_1(B_146) | ~m1_subset_1(B_146, k1_zfmisc_1(A_147)) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.95/3.82  tff(c_846, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_840])).
% 9.95/3.82  tff(c_850, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_846])).
% 9.95/3.82  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.95/3.82  tff(c_12446, plain, (![A_1314, B_1315, C_1316, D_1317]: (k7_relset_1(A_1314, B_1315, C_1316, D_1317)=k9_relat_1(C_1316, D_1317) | ~m1_subset_1(C_1316, k1_zfmisc_1(k2_zfmisc_1(A_1314, B_1315))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.95/3.82  tff(c_12458, plain, (![D_1318]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_1318)=k9_relat_1('#skF_5', D_1318))), inference(resolution, [status(thm)], [c_70, c_12446])).
% 9.95/3.82  tff(c_9436, plain, (![A_1051, B_1052, C_1053, D_1054]: (k2_partfun1(A_1051, B_1052, C_1053, D_1054)=k7_relat_1(C_1053, D_1054) | ~m1_subset_1(C_1053, k1_zfmisc_1(k2_zfmisc_1(A_1051, B_1052))) | ~v1_funct_1(C_1053))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.95/3.82  tff(c_9443, plain, (![D_1054]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1054)=k7_relat_1('#skF_5', D_1054) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_9436])).
% 9.95/3.82  tff(c_9454, plain, (![D_1054]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1054)=k7_relat_1('#skF_5', D_1054))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_9443])).
% 9.95/3.82  tff(c_68, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.95/3.82  tff(c_24, plain, (![A_11, B_12]: (v1_relat_1(k7_relat_1(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.95/3.82  tff(c_7031, plain, (![C_799, A_800, B_801]: (m1_subset_1(C_799, k1_zfmisc_1(k2_zfmisc_1(A_800, B_801))) | ~r1_tarski(k2_relat_1(C_799), B_801) | ~r1_tarski(k1_relat_1(C_799), A_800) | ~v1_relat_1(C_799))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.95/3.82  tff(c_6913, plain, (![A_779, B_780, C_781, D_782]: (k2_partfun1(A_779, B_780, C_781, D_782)=k7_relat_1(C_781, D_782) | ~m1_subset_1(C_781, k1_zfmisc_1(k2_zfmisc_1(A_779, B_780))) | ~v1_funct_1(C_781))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.95/3.82  tff(c_6918, plain, (![D_782]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_782)=k7_relat_1('#skF_5', D_782) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_6913])).
% 9.95/3.82  tff(c_6926, plain, (![D_782]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_782)=k7_relat_1('#skF_5', D_782))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6918])).
% 9.95/3.82  tff(c_796, plain, (![A_139, B_140, C_141, D_142]: (v1_funct_1(k2_partfun1(A_139, B_140, C_141, D_142)) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_1(C_141))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.95/3.82  tff(c_801, plain, (![D_142]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_142)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_796])).
% 9.95/3.82  tff(c_809, plain, (![D_142]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_142)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_801])).
% 9.95/3.82  tff(c_64, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.95/3.82  tff(c_142, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_64])).
% 9.95/3.82  tff(c_812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_809, c_142])).
% 9.95/3.82  tff(c_813, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_64])).
% 9.95/3.82  tff(c_4535, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_813])).
% 9.95/3.82  tff(c_6929, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6926, c_4535])).
% 9.95/3.82  tff(c_7062, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_7031, c_6929])).
% 9.95/3.82  tff(c_7113, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_7062])).
% 9.95/3.82  tff(c_7116, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_7113])).
% 9.95/3.82  tff(c_7120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_850, c_7116])).
% 9.95/3.82  tff(c_7122, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitRight, [status(thm)], [c_7062])).
% 9.95/3.82  tff(c_76, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.95/3.82  tff(c_72, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.95/3.82  tff(c_4983, plain, (![A_601, B_602, C_603]: (k1_relset_1(A_601, B_602, C_603)=k1_relat_1(C_603) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_601, B_602))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.95/3.82  tff(c_4998, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_4983])).
% 9.95/3.82  tff(c_5513, plain, (![B_681, A_682, C_683]: (k1_xboole_0=B_681 | k1_relset_1(A_682, B_681, C_683)=A_682 | ~v1_funct_2(C_683, A_682, B_681) | ~m1_subset_1(C_683, k1_zfmisc_1(k2_zfmisc_1(A_682, B_681))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.95/3.82  tff(c_5523, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_5513])).
% 9.95/3.82  tff(c_5534, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4998, c_5523])).
% 9.95/3.82  tff(c_5536, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_5534])).
% 9.95/3.82  tff(c_4497, plain, (![C_547, A_548, B_549]: (v4_relat_1(C_547, A_548) | ~m1_subset_1(C_547, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.95/3.82  tff(c_4512, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_4497])).
% 9.95/3.82  tff(c_4633, plain, (![B_577, A_578]: (k7_relat_1(B_577, A_578)=B_577 | ~v4_relat_1(B_577, A_578) | ~v1_relat_1(B_577))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.95/3.82  tff(c_4645, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4512, c_4633])).
% 9.95/3.82  tff(c_4655, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_850, c_4645])).
% 9.95/3.82  tff(c_32, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(k7_relat_1(B_20, A_19)), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.95/3.82  tff(c_4691, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4655, c_32])).
% 9.95/3.82  tff(c_4700, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_850, c_4691])).
% 9.95/3.82  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.95/3.82  tff(c_4714, plain, (k1_relat_1('#skF_5')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4700, c_4])).
% 9.95/3.82  tff(c_4760, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4714])).
% 9.95/3.82  tff(c_5538, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5536, c_4760])).
% 9.95/3.82  tff(c_5542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_5538])).
% 9.95/3.82  tff(c_5543, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5534])).
% 9.95/3.82  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.95/3.82  tff(c_5584, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5543, c_2])).
% 9.95/3.82  tff(c_5586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_5584])).
% 9.95/3.82  tff(c_5587, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitRight, [status(thm)], [c_4714])).
% 9.95/3.82  tff(c_5676, plain, (![B_690, A_691]: (k1_relat_1(k7_relat_1(B_690, A_691))=A_691 | ~r1_tarski(A_691, k1_relat_1(B_690)) | ~v1_relat_1(B_690))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.95/3.82  tff(c_5683, plain, (![A_691]: (k1_relat_1(k7_relat_1('#skF_5', A_691))=A_691 | ~r1_tarski(A_691, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5587, c_5676])).
% 9.95/3.82  tff(c_5704, plain, (![A_691]: (k1_relat_1(k7_relat_1('#skF_5', A_691))=A_691 | ~r1_tarski(A_691, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_850, c_5683])).
% 9.95/3.82  tff(c_5811, plain, (![B_701]: (k1_relat_1(k7_relat_1(B_701, k1_relat_1(B_701)))=k1_relat_1(B_701) | ~v1_relat_1(B_701))), inference(resolution, [status(thm)], [c_8, c_5676])).
% 9.95/3.82  tff(c_6074, plain, (![A_717]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_5', A_717), A_717))=k1_relat_1(k7_relat_1('#skF_5', A_717)) | ~v1_relat_1(k7_relat_1('#skF_5', A_717)) | ~r1_tarski(A_717, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5704, c_5811])).
% 9.95/3.82  tff(c_6104, plain, (![A_717]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_5', A_717)), A_717) | ~v1_relat_1(k7_relat_1('#skF_5', A_717)) | ~v1_relat_1(k7_relat_1('#skF_5', A_717)) | ~r1_tarski(A_717, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6074, c_32])).
% 9.95/3.82  tff(c_6862, plain, (![A_766, B_767, C_768, D_769]: (k7_relset_1(A_766, B_767, C_768, D_769)=k9_relat_1(C_768, D_769) | ~m1_subset_1(C_768, k1_zfmisc_1(k2_zfmisc_1(A_766, B_767))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.95/3.82  tff(c_6873, plain, (![D_769]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_769)=k9_relat_1('#skF_5', D_769))), inference(resolution, [status(thm)], [c_70, c_6862])).
% 9.95/3.82  tff(c_66, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.95/3.82  tff(c_6876, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6873, c_66])).
% 9.95/3.82  tff(c_28, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.95/3.82  tff(c_7121, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_7062])).
% 9.95/3.82  tff(c_7140, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_7121])).
% 9.95/3.82  tff(c_7143, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28, c_7140])).
% 9.95/3.82  tff(c_7146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_850, c_6876, c_7143])).
% 9.95/3.82  tff(c_7147, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_7121])).
% 9.95/3.82  tff(c_7193, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_6104, c_7147])).
% 9.95/3.82  tff(c_7203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_7122, c_7193])).
% 9.95/3.82  tff(c_7204, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_813])).
% 9.95/3.82  tff(c_9467, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9454, c_7204])).
% 9.95/3.82  tff(c_7704, plain, (![A_863, B_864, C_865]: (k1_relset_1(A_863, B_864, C_865)=k1_relat_1(C_865) | ~m1_subset_1(C_865, k1_zfmisc_1(k2_zfmisc_1(A_863, B_864))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.95/3.82  tff(c_7723, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_7704])).
% 9.95/3.82  tff(c_8393, plain, (![B_947, A_948, C_949]: (k1_xboole_0=B_947 | k1_relset_1(A_948, B_947, C_949)=A_948 | ~v1_funct_2(C_949, A_948, B_947) | ~m1_subset_1(C_949, k1_zfmisc_1(k2_zfmisc_1(A_948, B_947))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.95/3.82  tff(c_8406, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_8393])).
% 9.95/3.82  tff(c_8419, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7723, c_8406])).
% 9.95/3.82  tff(c_8421, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_8419])).
% 9.95/3.82  tff(c_7239, plain, (![B_825, A_826]: (k7_relat_1(B_825, A_826)=B_825 | ~v4_relat_1(B_825, A_826) | ~v1_relat_1(B_825))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.95/3.82  tff(c_7245, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4512, c_7239])).
% 9.95/3.82  tff(c_7249, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_850, c_7245])).
% 9.95/3.82  tff(c_7260, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7249, c_32])).
% 9.95/3.82  tff(c_7267, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_850, c_7260])).
% 9.95/3.82  tff(c_7305, plain, (k1_relat_1('#skF_5')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_7267, c_4])).
% 9.95/3.82  tff(c_7352, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_7305])).
% 9.95/3.82  tff(c_8423, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8421, c_7352])).
% 9.95/3.82  tff(c_8427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_8423])).
% 9.95/3.82  tff(c_8428, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_8419])).
% 9.95/3.82  tff(c_8470, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8428, c_2])).
% 9.95/3.82  tff(c_8472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_8470])).
% 9.95/3.82  tff(c_8473, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitRight, [status(thm)], [c_7305])).
% 9.95/3.82  tff(c_8662, plain, (![B_961, A_962]: (k1_relat_1(k7_relat_1(B_961, A_962))=A_962 | ~r1_tarski(A_962, k1_relat_1(B_961)) | ~v1_relat_1(B_961))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.95/3.82  tff(c_8669, plain, (![A_962]: (k1_relat_1(k7_relat_1('#skF_5', A_962))=A_962 | ~r1_tarski(A_962, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8473, c_8662])).
% 9.95/3.82  tff(c_8690, plain, (![A_962]: (k1_relat_1(k7_relat_1('#skF_5', A_962))=A_962 | ~r1_tarski(A_962, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_850, c_8669])).
% 9.95/3.82  tff(c_7205, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_813])).
% 9.95/3.82  tff(c_22, plain, (![B_10, A_8]: (v1_relat_1(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.95/3.82  tff(c_8483, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_7205, c_22])).
% 9.95/3.82  tff(c_8491, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8483])).
% 9.95/3.82  tff(c_9465, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9454, c_8491])).
% 9.95/3.82  tff(c_38, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.95/3.82  tff(c_8488, plain, (v4_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_7205, c_38])).
% 9.95/3.82  tff(c_9463, plain, (v4_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9454, c_8488])).
% 9.95/3.82  tff(c_30, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.95/3.82  tff(c_9483, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_2')=k7_relat_1('#skF_5', '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_9463, c_30])).
% 9.95/3.82  tff(c_9486, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_2')=k7_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9465, c_9483])).
% 9.95/3.82  tff(c_876, plain, (![B_150, A_151]: (r1_tarski(k1_relat_1(k7_relat_1(B_150, A_151)), A_151) | ~v1_relat_1(B_150))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.95/3.82  tff(c_888, plain, (![B_150, A_151]: (k1_relat_1(k7_relat_1(B_150, A_151))=A_151 | ~r1_tarski(A_151, k1_relat_1(k7_relat_1(B_150, A_151))) | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_876, c_4])).
% 9.95/3.82  tff(c_9602, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9486, c_888])).
% 9.95/3.82  tff(c_9618, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1(k7_relat_1('#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9465, c_9486, c_9602])).
% 9.95/3.82  tff(c_9698, plain, (~r1_tarski('#skF_2', k1_relat_1(k7_relat_1('#skF_5', '#skF_2')))), inference(splitLeft, [status(thm)], [c_9618])).
% 9.95/3.82  tff(c_9702, plain, (~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8690, c_9698])).
% 9.95/3.82  tff(c_9705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_8, c_9702])).
% 9.95/3.82  tff(c_9706, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_9618])).
% 9.95/3.82  tff(c_8882, plain, (![A_977, B_978, C_979]: (k1_relset_1(A_977, B_978, C_979)=k1_relat_1(C_979) | ~m1_subset_1(C_979, k1_zfmisc_1(k2_zfmisc_1(A_977, B_978))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.95/3.82  tff(c_8899, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_7205, c_8882])).
% 9.95/3.82  tff(c_9460, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9454, c_9454, c_8899])).
% 9.95/3.82  tff(c_9708, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9706, c_9460])).
% 9.95/3.82  tff(c_9466, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9454, c_7205])).
% 9.95/3.82  tff(c_9843, plain, (![B_1069, C_1070, A_1071]: (k1_xboole_0=B_1069 | v1_funct_2(C_1070, A_1071, B_1069) | k1_relset_1(A_1071, B_1069, C_1070)!=A_1071 | ~m1_subset_1(C_1070, k1_zfmisc_1(k2_zfmisc_1(A_1071, B_1069))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.95/3.82  tff(c_9846, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_9466, c_9843])).
% 9.95/3.82  tff(c_9865, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9708, c_9846])).
% 9.95/3.82  tff(c_9866, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_9467, c_9865])).
% 9.95/3.82  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.95/3.82  tff(c_9913, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9866, c_10])).
% 9.95/3.82  tff(c_9382, plain, (![A_1038, B_1039, C_1040, D_1041]: (k7_relset_1(A_1038, B_1039, C_1040, D_1041)=k9_relat_1(C_1040, D_1041) | ~m1_subset_1(C_1040, k1_zfmisc_1(k2_zfmisc_1(A_1038, B_1039))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.95/3.82  tff(c_9396, plain, (![D_1041]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_1041)=k9_relat_1('#skF_5', D_1041))), inference(resolution, [status(thm)], [c_70, c_9382])).
% 9.95/3.82  tff(c_123, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.95/3.82  tff(c_135, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_123])).
% 9.95/3.82  tff(c_4496, plain, (~r1_tarski('#skF_3', k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_135])).
% 9.95/3.82  tff(c_9397, plain, (~r1_tarski('#skF_3', k9_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9396, c_4496])).
% 9.95/3.82  tff(c_9923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9913, c_9397])).
% 9.95/3.82  tff(c_9924, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_135])).
% 9.95/3.82  tff(c_12464, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_12458, c_9924])).
% 9.95/3.82  tff(c_12880, plain, (![A_1373, B_1374, C_1375, D_1376]: (k2_partfun1(A_1373, B_1374, C_1375, D_1376)=k7_relat_1(C_1375, D_1376) | ~m1_subset_1(C_1375, k1_zfmisc_1(k2_zfmisc_1(A_1373, B_1374))) | ~v1_funct_1(C_1375))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.95/3.82  tff(c_12887, plain, (![D_1376]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1376)=k7_relat_1('#skF_5', D_1376) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_12880])).
% 9.95/3.82  tff(c_12896, plain, (![D_1376]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1376)=k7_relat_1('#skF_5', D_1376))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_12887])).
% 9.95/3.82  tff(c_12756, plain, (![A_1358, B_1359, C_1360, D_1361]: (k2_partfun1(A_1358, B_1359, C_1360, D_1361)=k7_relat_1(C_1360, D_1361) | ~m1_subset_1(C_1360, k1_zfmisc_1(k2_zfmisc_1(A_1358, B_1359))) | ~v1_funct_1(C_1360))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.95/3.82  tff(c_12763, plain, (![D_1361]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1361)=k7_relat_1('#skF_5', D_1361) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_12756])).
% 9.95/3.82  tff(c_12772, plain, (![D_1361]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1361)=k7_relat_1('#skF_5', D_1361))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_12763])).
% 9.95/3.82  tff(c_12559, plain, (![C_1334, A_1335, B_1336]: (m1_subset_1(C_1334, k1_zfmisc_1(k2_zfmisc_1(A_1335, B_1336))) | ~r1_tarski(k2_relat_1(C_1334), B_1336) | ~r1_tarski(k1_relat_1(C_1334), A_1335) | ~v1_relat_1(C_1334))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.95/3.82  tff(c_9957, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_813])).
% 9.95/3.82  tff(c_12591, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_12559, c_9957])).
% 9.95/3.82  tff(c_12663, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_12591])).
% 9.95/3.82  tff(c_12828, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12772, c_12663])).
% 9.95/3.82  tff(c_12847, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_12828])).
% 9.95/3.82  tff(c_12851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_850, c_12847])).
% 9.95/3.82  tff(c_12853, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitRight, [status(thm)], [c_12591])).
% 9.95/3.82  tff(c_12897, plain, (v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12896, c_12853])).
% 9.95/3.82  tff(c_10338, plain, (![A_1122, B_1123, C_1124]: (k1_relset_1(A_1122, B_1123, C_1124)=k1_relat_1(C_1124) | ~m1_subset_1(C_1124, k1_zfmisc_1(k2_zfmisc_1(A_1122, B_1123))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.95/3.82  tff(c_10353, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_10338])).
% 9.95/3.82  tff(c_10976, plain, (![B_1209, A_1210, C_1211]: (k1_xboole_0=B_1209 | k1_relset_1(A_1210, B_1209, C_1211)=A_1210 | ~v1_funct_2(C_1211, A_1210, B_1209) | ~m1_subset_1(C_1211, k1_zfmisc_1(k2_zfmisc_1(A_1210, B_1209))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.95/3.82  tff(c_10986, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_10976])).
% 9.95/3.82  tff(c_10997, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_10353, c_10986])).
% 9.95/3.82  tff(c_10999, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_10997])).
% 9.95/3.82  tff(c_9934, plain, (![C_1072, A_1073, B_1074]: (v4_relat_1(C_1072, A_1073) | ~m1_subset_1(C_1072, k1_zfmisc_1(k2_zfmisc_1(A_1073, B_1074))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.95/3.82  tff(c_9949, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_9934])).
% 9.95/3.82  tff(c_10010, plain, (![B_1089, A_1090]: (k7_relat_1(B_1089, A_1090)=B_1089 | ~v4_relat_1(B_1089, A_1090) | ~v1_relat_1(B_1089))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.95/3.82  tff(c_10022, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_9949, c_10010])).
% 9.95/3.82  tff(c_10032, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_850, c_10022])).
% 9.95/3.82  tff(c_10039, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10032, c_32])).
% 9.95/3.82  tff(c_10048, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_850, c_10039])).
% 9.95/3.82  tff(c_10091, plain, (k1_relat_1('#skF_5')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10048, c_4])).
% 9.95/3.82  tff(c_10130, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_10091])).
% 9.95/3.82  tff(c_11001, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10999, c_10130])).
% 9.95/3.82  tff(c_11005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_11001])).
% 9.95/3.82  tff(c_11006, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_10997])).
% 9.95/3.82  tff(c_11047, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11006, c_2])).
% 9.95/3.82  tff(c_11049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_11047])).
% 9.95/3.82  tff(c_11050, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitRight, [status(thm)], [c_10091])).
% 9.95/3.82  tff(c_11126, plain, (![B_1219, A_1220]: (k1_relat_1(k7_relat_1(B_1219, A_1220))=A_1220 | ~r1_tarski(A_1220, k1_relat_1(B_1219)) | ~v1_relat_1(B_1219))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.95/3.82  tff(c_11129, plain, (![A_1220]: (k1_relat_1(k7_relat_1('#skF_5', A_1220))=A_1220 | ~r1_tarski(A_1220, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11050, c_11126])).
% 9.95/3.82  tff(c_11149, plain, (![A_1220]: (k1_relat_1(k7_relat_1('#skF_5', A_1220))=A_1220 | ~r1_tarski(A_1220, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_850, c_11129])).
% 9.95/3.82  tff(c_11313, plain, (![B_1236]: (k1_relat_1(k7_relat_1(B_1236, k1_relat_1(B_1236)))=k1_relat_1(B_1236) | ~v1_relat_1(B_1236))), inference(resolution, [status(thm)], [c_8, c_11126])).
% 9.95/3.82  tff(c_11399, plain, (![A_1239]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_5', A_1239), A_1239))=k1_relat_1(k7_relat_1('#skF_5', A_1239)) | ~v1_relat_1(k7_relat_1('#skF_5', A_1239)) | ~r1_tarski(A_1239, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11149, c_11313])).
% 9.95/3.82  tff(c_11418, plain, (![A_1239]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_5', A_1239)), A_1239) | ~v1_relat_1(k7_relat_1('#skF_5', A_1239)) | ~v1_relat_1(k7_relat_1('#skF_5', A_1239)) | ~r1_tarski(A_1239, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11399, c_32])).
% 9.95/3.82  tff(c_44, plain, (![C_35, A_33, B_34]: (m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~r1_tarski(k2_relat_1(C_35), B_34) | ~r1_tarski(k1_relat_1(C_35), A_33) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.95/3.82  tff(c_12900, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12896, c_9957])).
% 9.95/3.82  tff(c_12916, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_12900])).
% 9.95/3.82  tff(c_12922, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12897, c_12916])).
% 9.95/3.82  tff(c_12924, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_12922])).
% 9.95/3.82  tff(c_12927, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_11418, c_12924])).
% 9.95/3.82  tff(c_12937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_12897, c_12927])).
% 9.95/3.82  tff(c_12938, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_12922])).
% 9.95/3.82  tff(c_12977, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28, c_12938])).
% 9.95/3.82  tff(c_12980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_850, c_8, c_12464, c_12977])).
% 9.95/3.82  tff(c_12981, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_813])).
% 9.95/3.82  tff(c_15392, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15379, c_12981])).
% 9.95/3.82  tff(c_13502, plain, (![A_1433, B_1434, C_1435]: (k1_relset_1(A_1433, B_1434, C_1435)=k1_relat_1(C_1435) | ~m1_subset_1(C_1435, k1_zfmisc_1(k2_zfmisc_1(A_1433, B_1434))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.95/3.82  tff(c_13521, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_13502])).
% 9.95/3.82  tff(c_14161, plain, (![B_1528, A_1529, C_1530]: (k1_xboole_0=B_1528 | k1_relset_1(A_1529, B_1528, C_1530)=A_1529 | ~v1_funct_2(C_1530, A_1529, B_1528) | ~m1_subset_1(C_1530, k1_zfmisc_1(k2_zfmisc_1(A_1529, B_1528))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.95/3.82  tff(c_14171, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_14161])).
% 9.95/3.82  tff(c_14182, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_13521, c_14171])).
% 9.95/3.82  tff(c_14184, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_14182])).
% 9.95/3.82  tff(c_13042, plain, (![B_1395, A_1396]: (k7_relat_1(B_1395, A_1396)=B_1395 | ~v4_relat_1(B_1395, A_1396) | ~v1_relat_1(B_1395))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.95/3.82  tff(c_13054, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_9949, c_13042])).
% 9.95/3.82  tff(c_13064, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_850, c_13054])).
% 9.95/3.82  tff(c_13068, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13064, c_32])).
% 9.95/3.82  tff(c_13075, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_850, c_13068])).
% 9.95/3.82  tff(c_13113, plain, (k1_relat_1('#skF_5')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_13075, c_4])).
% 9.95/3.82  tff(c_13175, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_13113])).
% 9.95/3.82  tff(c_14186, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14184, c_13175])).
% 9.95/3.82  tff(c_14190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_14186])).
% 9.95/3.82  tff(c_14191, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_14182])).
% 9.95/3.82  tff(c_14236, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14191, c_2])).
% 9.95/3.82  tff(c_14238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_14236])).
% 9.95/3.82  tff(c_14239, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitRight, [status(thm)], [c_13113])).
% 9.95/3.82  tff(c_14445, plain, (![B_1550, A_1551]: (k1_relat_1(k7_relat_1(B_1550, A_1551))=A_1551 | ~r1_tarski(A_1551, k1_relat_1(B_1550)) | ~v1_relat_1(B_1550))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.95/3.82  tff(c_14452, plain, (![A_1551]: (k1_relat_1(k7_relat_1('#skF_5', A_1551))=A_1551 | ~r1_tarski(A_1551, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14239, c_14445])).
% 9.95/3.82  tff(c_14473, plain, (![A_1551]: (k1_relat_1(k7_relat_1('#skF_5', A_1551))=A_1551 | ~r1_tarski(A_1551, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_850, c_14452])).
% 9.95/3.82  tff(c_15265, plain, (![A_1644, B_1645, C_1646, D_1647]: (k2_partfun1(A_1644, B_1645, C_1646, D_1647)=k7_relat_1(C_1646, D_1647) | ~m1_subset_1(C_1646, k1_zfmisc_1(k2_zfmisc_1(A_1644, B_1645))) | ~v1_funct_1(C_1646))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.95/3.82  tff(c_15274, plain, (![D_1647]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1647)=k7_relat_1('#skF_5', D_1647) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_15265])).
% 9.95/3.82  tff(c_15286, plain, (![D_1647]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1647)=k7_relat_1('#skF_5', D_1647))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_15274])).
% 9.95/3.82  tff(c_12982, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_813])).
% 9.95/3.82  tff(c_13159, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12982, c_22])).
% 9.95/3.82  tff(c_13167, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_13159])).
% 9.95/3.82  tff(c_13164, plain, (v4_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_12982, c_38])).
% 9.95/3.82  tff(c_13171, plain, (k7_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2')=k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_13164, c_30])).
% 9.95/3.82  tff(c_13174, plain, (k7_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2')=k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13167, c_13171])).
% 9.95/3.82  tff(c_15043, plain, (![B_1602, A_1603]: (k1_relat_1(k7_relat_1(B_1602, A_1603))=A_1603 | ~r1_tarski(A_1603, k1_relat_1(k7_relat_1(B_1602, A_1603))) | ~v1_relat_1(B_1602))), inference(resolution, [status(thm)], [c_876, c_4])).
% 9.95/3.82  tff(c_15046, plain, (k1_relat_1(k7_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))) | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13174, c_15043])).
% 9.95/3.82  tff(c_15070, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_13167, c_13174, c_15046])).
% 9.95/3.82  tff(c_15231, plain, (~r1_tarski('#skF_2', k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')))), inference(splitLeft, [status(thm)], [c_15070])).
% 9.95/3.82  tff(c_15287, plain, (~r1_tarski('#skF_2', k1_relat_1(k7_relat_1('#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_15286, c_15231])).
% 9.95/3.82  tff(c_15335, plain, (~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14473, c_15287])).
% 9.95/3.82  tff(c_15338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_8, c_15335])).
% 9.95/3.82  tff(c_15339, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_15070])).
% 9.95/3.82  tff(c_15380, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15379, c_15339])).
% 9.95/3.82  tff(c_18, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.95/3.82  tff(c_13168, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12982, c_18])).
% 9.95/3.82  tff(c_15387, plain, (r1_tarski(k7_relat_1('#skF_5', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15379, c_13168])).
% 9.95/3.82  tff(c_20, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.95/3.82  tff(c_14827, plain, (![A_1575, B_1576, C_1577]: (k1_relset_1(A_1575, B_1576, C_1577)=k1_relat_1(C_1577) | ~m1_subset_1(C_1577, k1_zfmisc_1(k2_zfmisc_1(A_1575, B_1576))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.95/3.82  tff(c_14845, plain, (![A_1575, B_1576, A_6]: (k1_relset_1(A_1575, B_1576, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_1575, B_1576)))), inference(resolution, [status(thm)], [c_20, c_14827])).
% 9.95/3.82  tff(c_15456, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_15387, c_14845])).
% 9.95/3.82  tff(c_15469, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15380, c_15456])).
% 9.95/3.82  tff(c_15391, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15379, c_12982])).
% 9.95/3.82  tff(c_15616, plain, (![B_1660, C_1661, A_1662]: (k1_xboole_0=B_1660 | v1_funct_2(C_1661, A_1662, B_1660) | k1_relset_1(A_1662, B_1660, C_1661)!=A_1662 | ~m1_subset_1(C_1661, k1_zfmisc_1(k2_zfmisc_1(A_1662, B_1660))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.95/3.82  tff(c_15619, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_15391, c_15616])).
% 9.95/3.82  tff(c_15638, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15469, c_15619])).
% 9.95/3.82  tff(c_15639, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_15392, c_15638])).
% 9.95/3.82  tff(c_15684, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_15639, c_10])).
% 9.95/3.82  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.95/3.82  tff(c_15683, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15639, c_15639, c_14])).
% 9.95/3.82  tff(c_14254, plain, (k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_13168, c_4])).
% 9.95/3.82  tff(c_14334, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_14254])).
% 9.95/3.82  tff(c_15386, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15379, c_14334])).
% 9.95/3.82  tff(c_15979, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15683, c_15386])).
% 9.95/3.82  tff(c_15983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15684, c_15979])).
% 9.95/3.82  tff(c_15984, plain, (k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_14254])).
% 9.95/3.82  tff(c_15991, plain, (~v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15984, c_12981])).
% 9.95/3.82  tff(c_18382, plain, (![A_1854, B_1855, C_1856, D_1857]: (k2_partfun1(A_1854, B_1855, C_1856, D_1857)=k7_relat_1(C_1856, D_1857) | ~m1_subset_1(C_1856, k1_zfmisc_1(k2_zfmisc_1(A_1854, B_1855))) | ~v1_funct_1(C_1856))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.95/3.82  tff(c_18389, plain, (![D_1857]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1857)=k7_relat_1('#skF_5', D_1857) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_18382])).
% 9.95/3.82  tff(c_18417, plain, (![D_1860]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1860)=k7_relat_1('#skF_5', D_1860))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_18389])).
% 9.95/3.82  tff(c_18423, plain, (k7_relat_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18417, c_15984])).
% 9.95/3.82  tff(c_16022, plain, (![B_1674, A_1675]: (k1_relat_1(k7_relat_1(B_1674, A_1675))=A_1675 | ~r1_tarski(A_1675, k1_relat_1(B_1674)) | ~v1_relat_1(B_1674))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.95/3.82  tff(c_16025, plain, (![A_1675]: (k1_relat_1(k7_relat_1('#skF_5', A_1675))=A_1675 | ~r1_tarski(A_1675, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14239, c_16022])).
% 9.95/3.82  tff(c_16045, plain, (![A_1675]: (k1_relat_1(k7_relat_1('#skF_5', A_1675))=A_1675 | ~r1_tarski(A_1675, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_850, c_16025])).
% 9.95/3.82  tff(c_18453, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18423, c_16045])).
% 9.95/3.82  tff(c_18475, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_18453])).
% 9.95/3.82  tff(c_16468, plain, (![A_1709, B_1710, C_1711]: (k1_relset_1(A_1709, B_1710, C_1711)=k1_relat_1(C_1711) | ~m1_subset_1(C_1711, k1_zfmisc_1(k2_zfmisc_1(A_1709, B_1710))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.95/3.82  tff(c_16577, plain, (![A_1722, B_1723, A_1724]: (k1_relset_1(A_1722, B_1723, A_1724)=k1_relat_1(A_1724) | ~r1_tarski(A_1724, k2_zfmisc_1(A_1722, B_1723)))), inference(resolution, [status(thm)], [c_20, c_16468])).
% 9.95/3.82  tff(c_16609, plain, (![A_1722, B_1723]: (k1_relset_1(A_1722, B_1723, k2_zfmisc_1(A_1722, B_1723))=k1_relat_1(k2_zfmisc_1(A_1722, B_1723)))), inference(resolution, [status(thm)], [c_8, c_16577])).
% 9.95/3.82  tff(c_15990, plain, (m1_subset_1(k2_zfmisc_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15984, c_12982])).
% 9.95/3.82  tff(c_18754, plain, (![B_1885, C_1886, A_1887]: (k1_xboole_0=B_1885 | v1_funct_2(C_1886, A_1887, B_1885) | k1_relset_1(A_1887, B_1885, C_1886)!=A_1887 | ~m1_subset_1(C_1886, k1_zfmisc_1(k2_zfmisc_1(A_1887, B_1885))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.95/3.82  tff(c_18760, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_15990, c_18754])).
% 9.95/3.82  tff(c_18777, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18475, c_16609, c_18760])).
% 9.95/3.82  tff(c_18778, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_15991, c_18777])).
% 9.95/3.82  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.95/3.82  tff(c_106, plain, (![A_52, B_53]: (v1_relat_1(k2_zfmisc_1(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.95/3.82  tff(c_108, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_106])).
% 9.95/3.82  tff(c_12989, plain, (![A_1386, A_1387, B_1388]: (v4_relat_1(A_1386, A_1387) | ~r1_tarski(A_1386, k2_zfmisc_1(A_1387, B_1388)))), inference(resolution, [status(thm)], [c_20, c_9934])).
% 9.95/3.82  tff(c_13014, plain, (![A_1387]: (v4_relat_1(k1_xboole_0, A_1387))), inference(resolution, [status(thm)], [c_10, c_12989])).
% 9.95/3.82  tff(c_13048, plain, (![A_1387]: (k7_relat_1(k1_xboole_0, A_1387)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_13014, c_13042])).
% 9.95/3.82  tff(c_13079, plain, (![A_1397]: (k7_relat_1(k1_xboole_0, A_1397)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_13048])).
% 9.95/3.82  tff(c_137, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_123])).
% 9.95/3.82  tff(c_887, plain, (![B_150]: (k1_relat_1(k7_relat_1(B_150, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_876, c_137])).
% 9.95/3.82  tff(c_13085, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13079, c_887])).
% 9.95/3.82  tff(c_13096, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_108, c_13085])).
% 9.95/3.82  tff(c_16598, plain, (![A_1722, B_1723]: (k1_relset_1(A_1722, B_1723, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_16577])).
% 9.95/3.82  tff(c_16608, plain, (![A_1722, B_1723]: (k1_relset_1(A_1722, B_1723, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13096, c_16598])).
% 9.95/3.82  tff(c_46, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_36, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.95/3.82  tff(c_79, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46])).
% 9.95/3.82  tff(c_14304, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_79])).
% 9.95/3.82  tff(c_14307, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_14304])).
% 9.95/3.82  tff(c_14311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_14307])).
% 9.95/3.82  tff(c_14313, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_79])).
% 9.95/3.82  tff(c_50, plain, (![C_38, B_37]: (v1_funct_2(C_38, k1_xboole_0, B_37) | k1_relset_1(k1_xboole_0, B_37, C_38)!=k1_xboole_0 | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_37))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.95/3.82  tff(c_16840, plain, (![C_1734, B_1735]: (v1_funct_2(C_1734, k1_xboole_0, B_1735) | k1_relset_1(k1_xboole_0, B_1735, C_1734)!=k1_xboole_0 | ~m1_subset_1(C_1734, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 9.95/3.82  tff(c_16842, plain, (![B_1735]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1735) | k1_relset_1(k1_xboole_0, B_1735, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14313, c_16840])).
% 9.95/3.82  tff(c_16848, plain, (![B_1735]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1735))), inference(demodulation, [status(thm), theory('equality')], [c_16608, c_16842])).
% 9.95/3.82  tff(c_18800, plain, (![B_1735]: (v1_funct_2('#skF_3', '#skF_3', B_1735))), inference(demodulation, [status(thm), theory('equality')], [c_18778, c_18778, c_16848])).
% 9.95/3.82  tff(c_18821, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18778, c_18778, c_13096])).
% 9.95/3.82  tff(c_18831, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18778, c_18778, c_14])).
% 9.95/3.82  tff(c_19169, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18831, c_18475])).
% 9.95/3.82  tff(c_19184, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18821, c_19169])).
% 9.95/3.82  tff(c_19174, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18831, c_15991])).
% 9.95/3.82  tff(c_19437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18800, c_19184, c_19174])).
% 9.95/3.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.95/3.82  
% 9.95/3.82  Inference rules
% 9.95/3.82  ----------------------
% 9.95/3.82  #Ref     : 0
% 9.95/3.82  #Sup     : 4122
% 9.95/3.82  #Fact    : 0
% 9.95/3.82  #Define  : 0
% 9.95/3.82  #Split   : 81
% 9.95/3.82  #Chain   : 0
% 9.95/3.82  #Close   : 0
% 9.95/3.82  
% 9.95/3.82  Ordering : KBO
% 9.95/3.82  
% 9.95/3.82  Simplification rules
% 9.95/3.82  ----------------------
% 9.95/3.82  #Subsume      : 347
% 9.95/3.82  #Demod        : 5439
% 9.95/3.82  #Tautology    : 2290
% 9.95/3.82  #SimpNegUnit  : 26
% 9.95/3.82  #BackRed      : 643
% 9.95/3.82  
% 9.95/3.82  #Partial instantiations: 0
% 9.95/3.82  #Strategies tried      : 1
% 9.95/3.82  
% 9.95/3.82  Timing (in seconds)
% 9.95/3.82  ----------------------
% 9.95/3.82  Preprocessing        : 0.46
% 9.95/3.82  Parsing              : 0.26
% 9.95/3.82  CNF conversion       : 0.03
% 9.95/3.82  Main loop            : 2.46
% 9.95/3.82  Inferencing          : 0.80
% 9.95/3.82  Reduction            : 0.93
% 9.95/3.82  Demodulation         : 0.67
% 9.95/3.82  BG Simplification    : 0.08
% 9.95/3.82  Subsumption          : 0.44
% 9.95/3.82  Abstraction          : 0.10
% 9.95/3.82  MUC search           : 0.00
% 9.95/3.82  Cooper               : 0.00
% 9.95/3.82  Total                : 3.03
% 9.95/3.82  Index Insertion      : 0.00
% 9.95/3.82  Index Deletion       : 0.00
% 9.95/3.82  Index Matching       : 0.00
% 9.95/3.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
