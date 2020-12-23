%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:14 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 656 expanded)
%              Number of leaves         :   42 ( 262 expanded)
%              Depth                    :   13
%              Number of atoms          :  196 (2376 expanded)
%              Number of equality atoms :   42 ( 239 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_151,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_131,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_40,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_109,axiom,(
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

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_99,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_44,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_36,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] :
      ( m1_subset_1(k1_partfun1(A_22,B_23,C_24,D_25,E_26,F_27),k1_zfmisc_1(k2_zfmisc_1(A_22,D_25)))
      | ~ m1_subset_1(F_27,k1_zfmisc_1(k2_zfmisc_1(C_24,D_25)))
      | ~ v1_funct_1(F_27)
      | ~ m1_subset_1(E_26,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_1(E_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_386,plain,(
    ! [D_81,C_82,A_83,B_84] :
      ( D_81 = C_82
      | ~ r2_relset_1(A_83,B_84,C_82,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_392,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_386])).

tff(c_403,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_392])).

tff(c_447,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_724,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_447])).

tff(c_731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_724])).

tff(c_732,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_1044,plain,(
    ! [D_192,B_194,A_190,E_193,C_191] :
      ( k1_xboole_0 = C_191
      | v2_funct_1(D_192)
      | ~ v2_funct_1(k1_partfun1(A_190,B_194,B_194,C_191,D_192,E_193))
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(B_194,C_191)))
      | ~ v1_funct_2(E_193,B_194,C_191)
      | ~ v1_funct_1(E_193)
      | ~ m1_subset_1(D_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_194)))
      | ~ v1_funct_2(D_192,A_190,B_194)
      | ~ v1_funct_1(D_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1046,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_1044])).

tff(c_1048,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_67,c_1046])).

tff(c_1049,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_1048])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1081,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1049,c_6])).

tff(c_146,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_161,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_146])).

tff(c_1242,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_161])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1344,plain,(
    ! [A_211] :
      ( A_211 = '#skF_1'
      | ~ r1_tarski(A_211,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1049,c_2])).

tff(c_1354,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1242,c_1344])).

tff(c_100,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_14])).

tff(c_119,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_67])).

tff(c_1077,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_119])).

tff(c_1380,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1354,c_1077])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1080,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1049,c_8])).

tff(c_162,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_146])).

tff(c_1188,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_162])).

tff(c_1355,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1188,c_1344])).

tff(c_1402,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1354,c_1355])).

tff(c_1406,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_99])).

tff(c_1425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1406])).

tff(c_1426,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1527,plain,(
    ! [C_226,A_227,B_228] :
      ( v1_relat_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1549,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1527])).

tff(c_1589,plain,(
    ! [C_234,B_235,A_236] :
      ( v5_relat_1(C_234,B_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_236,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1612,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1589])).

tff(c_1632,plain,(
    ! [A_242,B_243,D_244] :
      ( r2_relset_1(A_242,B_243,D_244,D_244)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1647,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_42,c_1632])).

tff(c_1701,plain,(
    ! [A_251,B_252,C_253] :
      ( k2_relset_1(A_251,B_252,C_253) = k2_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1724,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1701])).

tff(c_1743,plain,(
    ! [D_255,C_256,A_257,B_258] :
      ( D_255 = C_256
      | ~ r2_relset_1(A_257,B_258,C_256,D_255)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258)))
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1753,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_1743])).

tff(c_1772,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1753])).

tff(c_1801,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1772])).

tff(c_2093,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1801])).

tff(c_2100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_2093])).

tff(c_2101,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1772])).

tff(c_2493,plain,(
    ! [A_393,B_394,C_395,D_396] :
      ( k2_relset_1(A_393,B_394,C_395) = B_394
      | ~ r2_relset_1(B_394,B_394,k1_partfun1(B_394,A_393,A_393,B_394,D_396,C_395),k6_partfun1(B_394))
      | ~ m1_subset_1(D_396,k1_zfmisc_1(k2_zfmisc_1(B_394,A_393)))
      | ~ v1_funct_2(D_396,B_394,A_393)
      | ~ v1_funct_1(D_396)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394)))
      | ~ v1_funct_2(C_395,A_393,B_394)
      | ~ v1_funct_1(C_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2496,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2101,c_2493])).

tff(c_2501,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_1647,c_1724,c_2496])).

tff(c_32,plain,(
    ! [B_21] :
      ( v2_funct_2(B_21,k2_relat_1(B_21))
      | ~ v5_relat_1(B_21,k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2510,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2501,c_32])).

tff(c_2517,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_1612,c_2501,c_2510])).

tff(c_2519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1426,c_2517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:57:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.77  
% 4.23/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.78  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.23/1.78  
% 4.23/1.78  %Foreground sorts:
% 4.23/1.78  
% 4.23/1.78  
% 4.23/1.78  %Background operators:
% 4.23/1.78  
% 4.23/1.78  
% 4.23/1.78  %Foreground operators:
% 4.23/1.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.23/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.23/1.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.23/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.78  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.23/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.23/1.78  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.23/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.23/1.78  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.23/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.23/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.23/1.78  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.23/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.23/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.23/1.78  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.23/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.23/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.23/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.23/1.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.23/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.23/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.23/1.78  
% 4.71/1.80  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 4.71/1.80  tff(f_92, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.71/1.80  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.71/1.80  tff(f_86, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.71/1.80  tff(f_90, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.71/1.80  tff(f_66, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.71/1.80  tff(f_131, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 4.71/1.80  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.71/1.80  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.71/1.80  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.71/1.80  tff(f_40, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 4.71/1.80  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.71/1.80  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.71/1.80  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.71/1.80  tff(f_109, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.71/1.80  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.71/1.80  tff(c_52, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.71/1.80  tff(c_99, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 4.71/1.80  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.71/1.80  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.71/1.80  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.71/1.80  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.71/1.80  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.71/1.80  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.71/1.80  tff(c_44, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.71/1.80  tff(c_18, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.71/1.80  tff(c_67, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 4.71/1.80  tff(c_36, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (m1_subset_1(k1_partfun1(A_22, B_23, C_24, D_25, E_26, F_27), k1_zfmisc_1(k2_zfmisc_1(A_22, D_25))) | ~m1_subset_1(F_27, k1_zfmisc_1(k2_zfmisc_1(C_24, D_25))) | ~v1_funct_1(F_27) | ~m1_subset_1(E_26, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_1(E_26))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.71/1.80  tff(c_42, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.71/1.80  tff(c_54, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.71/1.80  tff(c_386, plain, (![D_81, C_82, A_83, B_84]: (D_81=C_82 | ~r2_relset_1(A_83, B_84, C_82, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.71/1.80  tff(c_392, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_54, c_386])).
% 4.71/1.80  tff(c_403, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_392])).
% 4.71/1.80  tff(c_447, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_403])).
% 4.71/1.80  tff(c_724, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_447])).
% 4.71/1.80  tff(c_731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_724])).
% 4.71/1.80  tff(c_732, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_403])).
% 4.71/1.80  tff(c_1044, plain, (![D_192, B_194, A_190, E_193, C_191]: (k1_xboole_0=C_191 | v2_funct_1(D_192) | ~v2_funct_1(k1_partfun1(A_190, B_194, B_194, C_191, D_192, E_193)) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(B_194, C_191))) | ~v1_funct_2(E_193, B_194, C_191) | ~v1_funct_1(E_193) | ~m1_subset_1(D_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_194))) | ~v1_funct_2(D_192, A_190, B_194) | ~v1_funct_1(D_192))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.71/1.80  tff(c_1046, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_732, c_1044])).
% 4.71/1.80  tff(c_1048, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_67, c_1046])).
% 4.71/1.80  tff(c_1049, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_99, c_1048])).
% 4.71/1.80  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.71/1.80  tff(c_1081, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_1049, c_6])).
% 4.71/1.80  tff(c_146, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.71/1.80  tff(c_161, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_146])).
% 4.71/1.80  tff(c_1242, plain, (r1_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_161])).
% 4.71/1.80  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.71/1.80  tff(c_1344, plain, (![A_211]: (A_211='#skF_1' | ~r1_tarski(A_211, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_1049, c_2])).
% 4.71/1.80  tff(c_1354, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_1242, c_1344])).
% 4.71/1.80  tff(c_100, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.71/1.80  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.71/1.80  tff(c_106, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_14])).
% 4.71/1.80  tff(c_119, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_67])).
% 4.71/1.80  tff(c_1077, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_119])).
% 4.71/1.80  tff(c_1380, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1354, c_1077])).
% 4.71/1.80  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.71/1.80  tff(c_1080, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_1049, c_8])).
% 4.71/1.80  tff(c_162, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_146])).
% 4.71/1.80  tff(c_1188, plain, (r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_162])).
% 4.71/1.80  tff(c_1355, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_1188, c_1344])).
% 4.71/1.80  tff(c_1402, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1354, c_1355])).
% 4.71/1.80  tff(c_1406, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_99])).
% 4.71/1.80  tff(c_1425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1406])).
% 4.71/1.80  tff(c_1426, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 4.71/1.80  tff(c_1527, plain, (![C_226, A_227, B_228]: (v1_relat_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.71/1.80  tff(c_1549, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1527])).
% 4.71/1.80  tff(c_1589, plain, (![C_234, B_235, A_236]: (v5_relat_1(C_234, B_235) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_236, B_235))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.71/1.80  tff(c_1612, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_1589])).
% 4.71/1.80  tff(c_1632, plain, (![A_242, B_243, D_244]: (r2_relset_1(A_242, B_243, D_244, D_244) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.71/1.80  tff(c_1647, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_42, c_1632])).
% 4.71/1.80  tff(c_1701, plain, (![A_251, B_252, C_253]: (k2_relset_1(A_251, B_252, C_253)=k2_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.71/1.80  tff(c_1724, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1701])).
% 4.71/1.80  tff(c_1743, plain, (![D_255, C_256, A_257, B_258]: (D_255=C_256 | ~r2_relset_1(A_257, B_258, C_256, D_255) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.71/1.80  tff(c_1753, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_54, c_1743])).
% 4.71/1.80  tff(c_1772, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1753])).
% 4.71/1.80  tff(c_1801, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1772])).
% 4.71/1.80  tff(c_2093, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1801])).
% 4.71/1.80  tff(c_2100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_2093])).
% 4.71/1.80  tff(c_2101, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1772])).
% 4.71/1.80  tff(c_2493, plain, (![A_393, B_394, C_395, D_396]: (k2_relset_1(A_393, B_394, C_395)=B_394 | ~r2_relset_1(B_394, B_394, k1_partfun1(B_394, A_393, A_393, B_394, D_396, C_395), k6_partfun1(B_394)) | ~m1_subset_1(D_396, k1_zfmisc_1(k2_zfmisc_1(B_394, A_393))) | ~v1_funct_2(D_396, B_394, A_393) | ~v1_funct_1(D_396) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))) | ~v1_funct_2(C_395, A_393, B_394) | ~v1_funct_1(C_395))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.71/1.80  tff(c_2496, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2101, c_2493])).
% 4.71/1.80  tff(c_2501, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_1647, c_1724, c_2496])).
% 4.71/1.80  tff(c_32, plain, (![B_21]: (v2_funct_2(B_21, k2_relat_1(B_21)) | ~v5_relat_1(B_21, k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.71/1.80  tff(c_2510, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2501, c_32])).
% 4.71/1.80  tff(c_2517, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1549, c_1612, c_2501, c_2510])).
% 4.71/1.80  tff(c_2519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1426, c_2517])).
% 4.71/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.80  
% 4.71/1.80  Inference rules
% 4.71/1.80  ----------------------
% 4.71/1.80  #Ref     : 0
% 4.71/1.80  #Sup     : 550
% 4.71/1.80  #Fact    : 0
% 4.71/1.80  #Define  : 0
% 4.71/1.80  #Split   : 8
% 4.71/1.80  #Chain   : 0
% 4.71/1.80  #Close   : 0
% 4.71/1.80  
% 4.71/1.80  Ordering : KBO
% 4.71/1.80  
% 4.71/1.80  Simplification rules
% 4.71/1.80  ----------------------
% 4.71/1.80  #Subsume      : 45
% 4.71/1.80  #Demod        : 423
% 4.71/1.80  #Tautology    : 221
% 4.71/1.80  #SimpNegUnit  : 3
% 4.71/1.80  #BackRed      : 87
% 4.71/1.80  
% 4.71/1.80  #Partial instantiations: 0
% 4.71/1.80  #Strategies tried      : 1
% 4.71/1.80  
% 4.71/1.80  Timing (in seconds)
% 4.71/1.80  ----------------------
% 4.71/1.80  Preprocessing        : 0.34
% 4.71/1.80  Parsing              : 0.18
% 4.71/1.80  CNF conversion       : 0.02
% 4.71/1.80  Main loop            : 0.69
% 4.71/1.80  Inferencing          : 0.24
% 4.71/1.80  Reduction            : 0.25
% 4.71/1.80  Demodulation         : 0.18
% 4.71/1.80  BG Simplification    : 0.03
% 4.71/1.80  Subsumption          : 0.11
% 4.71/1.80  Abstraction          : 0.03
% 4.71/1.80  MUC search           : 0.00
% 4.71/1.80  Cooper               : 0.00
% 4.71/1.80  Total                : 1.07
% 4.71/1.80  Index Insertion      : 0.00
% 4.71/1.80  Index Deletion       : 0.00
% 4.71/1.80  Index Matching       : 0.00
% 4.71/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
