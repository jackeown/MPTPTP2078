%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:49 EST 2020

% Result     : Theorem 14.22s
% Output     : CNFRefutation 14.97s
% Verified   : 
% Statistics : Number of formulae       :  697 (15330 expanded)
%              Number of leaves         :   36 (4573 expanded)
%              Depth                    :   24
%              Number of atoms          : 1348 (40349 expanded)
%              Number of equality atoms :  389 (14314 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_133,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(c_24,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_142,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_142])).

tff(c_152,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_148])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_43179,plain,(
    ! [A_2529,B_2530,C_2531] :
      ( k2_relset_1(A_2529,B_2530,C_2531) = k2_relat_1(C_2531)
      | ~ m1_subset_1(C_2531,k1_zfmisc_1(k2_zfmisc_1(A_2529,B_2530))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_43189,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_43179])).

tff(c_43198,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_43189])).

tff(c_32,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [A_14] :
      ( v1_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_153,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_156,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_153])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_156])).

tff(c_161,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_213,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_28,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_217,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_213])).

tff(c_3875,plain,(
    ! [A_296,B_297,C_298] :
      ( k2_relset_1(A_296,B_297,C_298) = k2_relat_1(C_298)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3885,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3875])).

tff(c_3895,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3885])).

tff(c_3837,plain,(
    ! [A_291,B_292,C_293] :
      ( k1_relset_1(A_291,B_292,C_293) = k1_relat_1(C_293)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3856,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3837])).

tff(c_6578,plain,(
    ! [B_444,A_445,C_446] :
      ( k1_xboole_0 = B_444
      | k1_relset_1(A_445,B_444,C_446) = A_445
      | ~ v1_funct_2(C_446,A_445,B_444)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_445,B_444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6591,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_6578])).

tff(c_6605,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3856,c_6591])).

tff(c_6621,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6605])).

tff(c_3607,plain,(
    ! [A_264] :
      ( k2_relat_1(k2_funct_1(A_264)) = k1_relat_1(A_264)
      | ~ v2_funct_1(A_264)
      | ~ v1_funct_1(A_264)
      | ~ v1_relat_1(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_277,plain,(
    ! [B_74,A_75] :
      ( v5_relat_1(B_74,A_75)
      | ~ r1_tarski(k2_relat_1(B_74),A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_286,plain,(
    ! [B_74] :
      ( v5_relat_1(B_74,k2_relat_1(B_74))
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_277])).

tff(c_7564,plain,(
    ! [A_535] :
      ( v5_relat_1(k2_funct_1(A_535),k1_relat_1(A_535))
      | ~ v1_relat_1(k2_funct_1(A_535))
      | ~ v2_funct_1(A_535)
      | ~ v1_funct_1(A_535)
      | ~ v1_relat_1(A_535) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3607,c_286])).

tff(c_7569,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6621,c_7564])).

tff(c_7575,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_7569])).

tff(c_7576,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7575])).

tff(c_7579,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_7576])).

tff(c_7583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_7579])).

tff(c_7585,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7575])).

tff(c_162,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_7584,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_7575])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7592,plain,(
    ! [A_536,A_537] :
      ( r1_tarski(k1_relat_1(A_536),A_537)
      | ~ v5_relat_1(k2_funct_1(A_536),A_537)
      | ~ v1_relat_1(k2_funct_1(A_536))
      | ~ v2_funct_1(A_536)
      | ~ v1_funct_1(A_536)
      | ~ v1_relat_1(A_536) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3607,c_22])).

tff(c_7731,plain,(
    ! [A_544] :
      ( r1_tarski(k1_relat_1(A_544),k2_relat_1(k2_funct_1(A_544)))
      | ~ v2_funct_1(A_544)
      | ~ v1_funct_1(A_544)
      | ~ v1_relat_1(A_544)
      | ~ v1_relat_1(k2_funct_1(A_544)) ) ),
    inference(resolution,[status(thm)],[c_286,c_7592])).

tff(c_7742,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6621,c_7731])).

tff(c_7753,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7585,c_152,c_70,c_64,c_7742])).

tff(c_230,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k2_relat_1(B_60),A_61)
      | ~ v5_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_237,plain,(
    ! [B_60,A_61] :
      ( k2_relat_1(B_60) = A_61
      | ~ r1_tarski(A_61,k2_relat_1(B_60))
      | ~ v5_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_230,c_2])).

tff(c_7757,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7753,c_237])).

tff(c_7768,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7585,c_7584,c_7757])).

tff(c_3735,plain,(
    ! [A_282] :
      ( m1_subset_1(A_282,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_282),k2_relat_1(A_282))))
      | ~ v1_funct_1(A_282)
      | ~ v1_relat_1(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3759,plain,(
    ! [A_282] :
      ( r1_tarski(A_282,k2_zfmisc_1(k1_relat_1(A_282),k2_relat_1(A_282)))
      | ~ v1_funct_1(A_282)
      | ~ v1_relat_1(A_282) ) ),
    inference(resolution,[status(thm)],[c_3735,c_14])).

tff(c_7836,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7768,c_3759])).

tff(c_7906,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7585,c_162,c_7836])).

tff(c_8078,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_7906])).

tff(c_8095,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_3895,c_8078])).

tff(c_8097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_8095])).

tff(c_8098,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6605])).

tff(c_4249,plain,(
    ! [B_325,A_326,C_327] :
      ( k1_xboole_0 = B_325
      | k1_relset_1(A_326,B_325,C_327) = A_326
      | ~ v1_funct_2(C_327,A_326,B_325)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_326,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4262,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_4249])).

tff(c_4276,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3856,c_4262])).

tff(c_4278,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4276])).

tff(c_4994,plain,(
    ! [A_394] :
      ( v5_relat_1(k2_funct_1(A_394),k1_relat_1(A_394))
      | ~ v1_relat_1(k2_funct_1(A_394))
      | ~ v2_funct_1(A_394)
      | ~ v1_funct_1(A_394)
      | ~ v1_relat_1(A_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3607,c_286])).

tff(c_4999,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4278,c_4994])).

tff(c_5005,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_4999])).

tff(c_5006,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5005])).

tff(c_5009,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_5006])).

tff(c_5013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_5009])).

tff(c_5015,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5005])).

tff(c_5014,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_5005])).

tff(c_5041,plain,(
    ! [A_395,A_396] :
      ( r1_tarski(k1_relat_1(A_395),A_396)
      | ~ v5_relat_1(k2_funct_1(A_395),A_396)
      | ~ v1_relat_1(k2_funct_1(A_395))
      | ~ v2_funct_1(A_395)
      | ~ v1_funct_1(A_395)
      | ~ v1_relat_1(A_395) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3607,c_22])).

tff(c_5906,plain,(
    ! [A_430] :
      ( r1_tarski(k1_relat_1(A_430),k2_relat_1(k2_funct_1(A_430)))
      | ~ v2_funct_1(A_430)
      | ~ v1_funct_1(A_430)
      | ~ v1_relat_1(A_430)
      | ~ v1_relat_1(k2_funct_1(A_430)) ) ),
    inference(resolution,[status(thm)],[c_286,c_5041])).

tff(c_5917,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4278,c_5906])).

tff(c_5928,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5015,c_152,c_70,c_64,c_5917])).

tff(c_5932,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5928,c_237])).

tff(c_5943,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5015,c_5014,c_5932])).

tff(c_6298,plain,(
    ! [A_431] :
      ( m1_subset_1(k2_funct_1(A_431),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_431),k2_relat_1(k2_funct_1(A_431)))))
      | ~ v1_funct_1(k2_funct_1(A_431))
      | ~ v1_relat_1(k2_funct_1(A_431))
      | ~ v2_funct_1(A_431)
      | ~ v1_funct_1(A_431)
      | ~ v1_relat_1(A_431) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3735])).

tff(c_6328,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5943,c_6298])).

tff(c_6351,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_5015,c_162,c_3895,c_6328])).

tff(c_6353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_6351])).

tff(c_6354,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4276])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( v5_relat_1(B_11,A_10)
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3922,plain,(
    ! [A_10] :
      ( v5_relat_1('#skF_3',A_10)
      | ~ r1_tarski('#skF_2',A_10)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3895,c_20])).

tff(c_3943,plain,(
    ! [A_10] :
      ( v5_relat_1('#skF_3',A_10)
      | ~ r1_tarski('#skF_2',A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_3922])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_190,plain,(
    ! [C_51,A_52,B_53] :
      ( v4_relat_1(C_51,A_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_288,plain,(
    ! [A_77,A_78,B_79] :
      ( v4_relat_1(A_77,A_78)
      | ~ r1_tarski(A_77,k2_zfmisc_1(A_78,B_79)) ) ),
    inference(resolution,[status(thm)],[c_16,c_190])).

tff(c_3680,plain,(
    ! [B_270,A_271,B_272] :
      ( v4_relat_1(k2_relat_1(B_270),A_271)
      | ~ v5_relat_1(B_270,k2_zfmisc_1(A_271,B_272))
      | ~ v1_relat_1(B_270) ) ),
    inference(resolution,[status(thm)],[c_22,c_288])).

tff(c_3695,plain,(
    ! [B_270,A_3] :
      ( v4_relat_1(k2_relat_1(B_270),A_3)
      | ~ v5_relat_1(B_270,k1_xboole_0)
      | ~ v1_relat_1(B_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3680])).

tff(c_3910,plain,(
    ! [A_3] :
      ( v4_relat_1('#skF_2',A_3)
      | ~ v5_relat_1('#skF_3',k1_xboole_0)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3895,c_3695])).

tff(c_3935,plain,(
    ! [A_3] :
      ( v4_relat_1('#skF_2',A_3)
      | ~ v5_relat_1('#skF_3',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_3910])).

tff(c_4015,plain,(
    ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3935])).

tff(c_4022,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3943,c_4015])).

tff(c_6368,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6354,c_4022])).

tff(c_6395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6368])).

tff(c_6397,plain,(
    v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3935])).

tff(c_3925,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_2',A_10)
      | ~ v5_relat_1('#skF_3',A_10)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3895,c_22])).

tff(c_3945,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_2',A_10)
      | ~ v5_relat_1('#skF_3',A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_3925])).

tff(c_6404,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6397,c_3945])).

tff(c_6417,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_6404,c_2])).

tff(c_6418,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6417])).

tff(c_8106,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8098,c_6418])).

tff(c_8134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8106])).

tff(c_8135,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6417])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_174,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_239,plain,(
    ! [C_64,B_65] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_174])).

tff(c_243,plain,(
    ! [A_5,B_65] :
      ( v5_relat_1(A_5,B_65)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_239])).

tff(c_3992,plain,(
    ! [A_302] :
      ( r1_tarski('#skF_2',A_302)
      | ~ v5_relat_1('#skF_3',A_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_3925])).

tff(c_4011,plain,(
    ! [B_65] :
      ( r1_tarski('#skF_2',B_65)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_243,c_3992])).

tff(c_4014,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4011])).

tff(c_8139,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8135,c_4014])).

tff(c_8159,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8135,c_8135,c_10])).

tff(c_3901,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3895,c_3759])).

tff(c_3929,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_3901])).

tff(c_8245,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8159,c_3929])).

tff(c_8250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8139,c_8245])).

tff(c_8251,plain,(
    ! [B_65] : r1_tarski('#skF_2',B_65) ),
    inference(splitRight,[status(thm)],[c_4011])).

tff(c_8394,plain,(
    ! [B_561,A_562,C_563] :
      ( k1_xboole_0 = B_561
      | k1_relset_1(A_562,B_561,C_563) = A_562
      | ~ v1_funct_2(C_563,A_562,B_561)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_562,B_561))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8404,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_8394])).

tff(c_8415,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3856,c_8404])).

tff(c_8431,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8415])).

tff(c_10900,plain,(
    ! [A_681] :
      ( v5_relat_1(k2_funct_1(A_681),k1_relat_1(A_681))
      | ~ v1_relat_1(k2_funct_1(A_681))
      | ~ v2_funct_1(A_681)
      | ~ v1_funct_1(A_681)
      | ~ v1_relat_1(A_681) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3607,c_286])).

tff(c_10905,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8431,c_10900])).

tff(c_10911,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_10905])).

tff(c_10928,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10911])).

tff(c_10931,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_10928])).

tff(c_10935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_10931])).

tff(c_10937,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10911])).

tff(c_10936,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_10911])).

tff(c_10912,plain,(
    ! [A_682,A_683] :
      ( r1_tarski(k1_relat_1(A_682),A_683)
      | ~ v5_relat_1(k2_funct_1(A_682),A_683)
      | ~ v1_relat_1(k2_funct_1(A_682))
      | ~ v2_funct_1(A_682)
      | ~ v1_funct_1(A_682)
      | ~ v1_relat_1(A_682) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3607,c_22])).

tff(c_11822,plain,(
    ! [A_696] :
      ( r1_tarski(k1_relat_1(A_696),k2_relat_1(k2_funct_1(A_696)))
      | ~ v2_funct_1(A_696)
      | ~ v1_funct_1(A_696)
      | ~ v1_relat_1(A_696)
      | ~ v1_relat_1(k2_funct_1(A_696)) ) ),
    inference(resolution,[status(thm)],[c_286,c_10912])).

tff(c_11833,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8431,c_11822])).

tff(c_11844,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10937,c_152,c_70,c_64,c_11833])).

tff(c_11848,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_11844,c_237])).

tff(c_11859,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10937,c_10936,c_11848])).

tff(c_11988,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11859,c_3759])).

tff(c_12068,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10937,c_162,c_11988])).

tff(c_12217,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_12068])).

tff(c_12234,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_3895,c_12217])).

tff(c_12236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_12234])).

tff(c_12237,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8415])).

tff(c_8252,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4011])).

tff(c_12240,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12237,c_8252])).

tff(c_12294,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_12240,c_2])).

tff(c_12300,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8251,c_12294])).

tff(c_12261,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12237,c_12237,c_10])).

tff(c_12445,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12300,c_12300,c_12261])).

tff(c_109,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_109])).

tff(c_121,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(B_40,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_113,c_121])).

tff(c_245,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_12314,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12300,c_245])).

tff(c_12547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12445,c_12314])).

tff(c_12548,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_12551,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12548,c_66])).

tff(c_16411,plain,(
    ! [A_959,B_960,C_961] :
      ( k1_relset_1(A_959,B_960,C_961) = k1_relat_1(C_961)
      | ~ m1_subset_1(C_961,k1_zfmisc_1(k2_zfmisc_1(A_959,B_960))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16455,plain,(
    ! [C_967] :
      ( k1_relset_1('#skF_1','#skF_2',C_967) = k1_relat_1(C_967)
      | ~ m1_subset_1(C_967,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12548,c_16411])).

tff(c_16463,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12551,c_16455])).

tff(c_16514,plain,(
    ! [A_974,B_975,C_976] :
      ( k2_relset_1(A_974,B_975,C_976) = k2_relat_1(C_976)
      | ~ m1_subset_1(C_976,k1_zfmisc_1(k2_zfmisc_1(A_974,B_975))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16558,plain,(
    ! [C_982] :
      ( k2_relset_1('#skF_1','#skF_2',C_982) = k2_relat_1(C_982)
      | ~ m1_subset_1(C_982,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12548,c_16514])).

tff(c_16561,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12551,c_16558])).

tff(c_16567,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16561])).

tff(c_20147,plain,(
    ! [B_1183,C_1184,A_1185] :
      ( k1_xboole_0 = B_1183
      | v1_funct_2(C_1184,A_1185,B_1183)
      | k1_relset_1(A_1185,B_1183,C_1184) != A_1185
      | ~ m1_subset_1(C_1184,k1_zfmisc_1(k2_zfmisc_1(A_1185,B_1183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_20156,plain,(
    ! [C_1184] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_1184,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_1184) != '#skF_1'
      | ~ m1_subset_1(C_1184,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12548,c_20147])).

tff(c_20260,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20156])).

tff(c_17104,plain,(
    ! [B_1028,A_1029,C_1030] :
      ( k1_xboole_0 = B_1028
      | k1_relset_1(A_1029,B_1028,C_1030) = A_1029
      | ~ v1_funct_2(C_1030,A_1029,B_1028)
      | ~ m1_subset_1(C_1030,k1_zfmisc_1(k2_zfmisc_1(A_1029,B_1028))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_17113,plain,(
    ! [C_1030] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_1030) = '#skF_1'
      | ~ v1_funct_2(C_1030,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1030,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12548,c_17104])).

tff(c_17622,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_17113])).

tff(c_16601,plain,(
    ! [A_10] :
      ( v5_relat_1('#skF_3',A_10)
      | ~ r1_tarski('#skF_2',A_10)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16567,c_20])).

tff(c_16668,plain,(
    ! [A_986] :
      ( v5_relat_1('#skF_3',A_986)
      | ~ r1_tarski('#skF_2',A_986) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_16601])).

tff(c_12650,plain,(
    ! [A_723,B_724,A_725] :
      ( v5_relat_1(A_723,B_724)
      | ~ r1_tarski(A_723,k2_zfmisc_1(A_725,B_724)) ) ),
    inference(resolution,[status(thm)],[c_16,c_174])).

tff(c_16270,plain,(
    ! [B_942,B_943,A_944] :
      ( v5_relat_1(k2_relat_1(B_942),B_943)
      | ~ v5_relat_1(B_942,k2_zfmisc_1(A_944,B_943))
      | ~ v1_relat_1(B_942) ) ),
    inference(resolution,[status(thm)],[c_22,c_12650])).

tff(c_16285,plain,(
    ! [B_942,B_4] :
      ( v5_relat_1(k2_relat_1(B_942),B_4)
      | ~ v5_relat_1(B_942,k1_xboole_0)
      | ~ v1_relat_1(B_942) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_16270])).

tff(c_16580,plain,(
    ! [B_4] :
      ( v5_relat_1('#skF_2',B_4)
      | ~ v5_relat_1('#skF_3',k1_xboole_0)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16567,c_16285])).

tff(c_16612,plain,(
    ! [B_4] :
      ( v5_relat_1('#skF_2',B_4)
      | ~ v5_relat_1('#skF_3',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_16580])).

tff(c_16631,plain,(
    ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_16612])).

tff(c_16681,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16668,c_16631])).

tff(c_17637,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17622,c_16681])).

tff(c_17673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_17637])).

tff(c_17933,plain,(
    ! [C_1082] :
      ( k1_relset_1('#skF_1','#skF_2',C_1082) = '#skF_1'
      | ~ v1_funct_2(C_1082,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1082,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_17113])).

tff(c_17936,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12551,c_17933])).

tff(c_17943,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16463,c_17936])).

tff(c_12684,plain,(
    ! [A_730] :
      ( k2_relat_1(k2_funct_1(A_730)) = k1_relat_1(A_730)
      | ~ v2_funct_1(A_730)
      | ~ v1_funct_1(A_730)
      | ~ v1_relat_1(A_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12593,plain,(
    ! [B_711,A_712] :
      ( v5_relat_1(B_711,A_712)
      | ~ r1_tarski(k2_relat_1(B_711),A_712)
      | ~ v1_relat_1(B_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12602,plain,(
    ! [B_711] :
      ( v5_relat_1(B_711,k2_relat_1(B_711))
      | ~ v1_relat_1(B_711) ) ),
    inference(resolution,[status(thm)],[c_6,c_12593])).

tff(c_18310,plain,(
    ! [A_1109] :
      ( v5_relat_1(k2_funct_1(A_1109),k1_relat_1(A_1109))
      | ~ v1_relat_1(k2_funct_1(A_1109))
      | ~ v2_funct_1(A_1109)
      | ~ v1_funct_1(A_1109)
      | ~ v1_relat_1(A_1109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12684,c_12602])).

tff(c_18318,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17943,c_18310])).

tff(c_18326,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_18318])).

tff(c_18327,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_18326])).

tff(c_18357,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_18327])).

tff(c_18361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_18357])).

tff(c_18363,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_18326])).

tff(c_30,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16134,plain,(
    ! [A_930] :
      ( m1_subset_1(A_930,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_930),k2_relat_1(A_930))))
      | ~ v1_funct_1(A_930)
      | ~ v1_relat_1(A_930) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_19504,plain,(
    ! [A_1141] :
      ( m1_subset_1(k2_funct_1(A_1141),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1141)),k1_relat_1(A_1141))))
      | ~ v1_funct_1(k2_funct_1(A_1141))
      | ~ v1_relat_1(k2_funct_1(A_1141))
      | ~ v2_funct_1(A_1141)
      | ~ v1_funct_1(A_1141)
      | ~ v1_relat_1(A_1141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_16134])).

tff(c_19531,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17943,c_19504])).

tff(c_19549,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_18363,c_162,c_19531])).

tff(c_19586,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_19549])).

tff(c_19603,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_16567,c_19586])).

tff(c_19605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_19603])).

tff(c_19607,plain,(
    v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_16612])).

tff(c_16604,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_2',A_10)
      | ~ v5_relat_1('#skF_3',A_10)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16567,c_22])).

tff(c_19675,plain,(
    ! [A_1146] :
      ( r1_tarski('#skF_2',A_1146)
      | ~ v5_relat_1('#skF_3',A_1146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_16604])).

tff(c_19694,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_19607,c_19675])).

tff(c_19721,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_19694,c_2])).

tff(c_19722,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_19721])).

tff(c_20278,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20260,c_19722])).

tff(c_20318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20278])).

tff(c_20320,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20156])).

tff(c_20211,plain,(
    ! [B_1194,A_1195,C_1196] :
      ( k1_xboole_0 = B_1194
      | k1_relset_1(A_1195,B_1194,C_1196) = A_1195
      | ~ v1_funct_2(C_1196,A_1195,B_1194)
      | ~ m1_subset_1(C_1196,k1_zfmisc_1(k2_zfmisc_1(A_1195,B_1194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_20220,plain,(
    ! [C_1196] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_1196) = '#skF_1'
      | ~ v1_funct_2(C_1196,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1196,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12548,c_20211])).

tff(c_20412,plain,(
    ! [C_1207] :
      ( k1_relset_1('#skF_1','#skF_2',C_1207) = '#skF_1'
      | ~ v1_funct_2(C_1207,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1207,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20320,c_20220])).

tff(c_20415,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12551,c_20412])).

tff(c_20422,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16463,c_20415])).

tff(c_21080,plain,(
    ! [A_1258] :
      ( v5_relat_1(k2_funct_1(A_1258),k1_relat_1(A_1258))
      | ~ v1_relat_1(k2_funct_1(A_1258))
      | ~ v2_funct_1(A_1258)
      | ~ v1_funct_1(A_1258)
      | ~ v1_relat_1(A_1258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12684,c_12602])).

tff(c_21088,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20422,c_21080])).

tff(c_21096,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_21088])).

tff(c_21097,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_21096])).

tff(c_21100,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_21097])).

tff(c_21104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_21100])).

tff(c_21106,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_21096])).

tff(c_21105,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_21096])).

tff(c_21011,plain,(
    ! [A_1253,A_1254] :
      ( r1_tarski(k1_relat_1(A_1253),A_1254)
      | ~ v5_relat_1(k2_funct_1(A_1253),A_1254)
      | ~ v1_relat_1(k2_funct_1(A_1253))
      | ~ v2_funct_1(A_1253)
      | ~ v1_funct_1(A_1253)
      | ~ v1_relat_1(A_1253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12684,c_22])).

tff(c_21264,plain,(
    ! [A_1268] :
      ( r1_tarski(k1_relat_1(A_1268),k2_relat_1(k2_funct_1(A_1268)))
      | ~ v2_funct_1(A_1268)
      | ~ v1_funct_1(A_1268)
      | ~ v1_relat_1(A_1268)
      | ~ v1_relat_1(k2_funct_1(A_1268)) ) ),
    inference(resolution,[status(thm)],[c_12602,c_21011])).

tff(c_21275,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20422,c_21264])).

tff(c_21286,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21106,c_152,c_70,c_64,c_21275])).

tff(c_21290,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_21286,c_237])).

tff(c_21301,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21106,c_21105,c_21290])).

tff(c_16158,plain,(
    ! [A_930] :
      ( r1_tarski(A_930,k2_zfmisc_1(k1_relat_1(A_930),k2_relat_1(A_930)))
      | ~ v1_funct_1(A_930)
      | ~ v1_relat_1(A_930) ) ),
    inference(resolution,[status(thm)],[c_16134,c_14])).

tff(c_21400,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21301,c_16158])).

tff(c_21481,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21106,c_162,c_21400])).

tff(c_21654,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_21481])).

tff(c_21671,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_16567,c_21654])).

tff(c_21673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_21671])).

tff(c_21674,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_19721])).

tff(c_16292,plain,(
    ! [A_5,B_943] :
      ( v5_relat_1(k2_relat_1(A_5),B_943)
      | ~ v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_243,c_16270])).

tff(c_16577,plain,(
    ! [B_943] :
      ( v5_relat_1('#skF_2',B_943)
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16567,c_16292])).

tff(c_16610,plain,(
    ! [B_943] :
      ( v5_relat_1('#skF_2',B_943)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_16577])).

tff(c_16630,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_16610])).

tff(c_21688,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21674,c_16630])).

tff(c_21716,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21674,c_21674,c_10])).

tff(c_16583,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16567,c_16158])).

tff(c_16614,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_16583])).

tff(c_21802,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21716,c_16614])).

tff(c_21804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21688,c_21802])).

tff(c_21806,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_16610])).

tff(c_21919,plain,(
    ! [A_1286] :
      ( r1_tarski('#skF_2',A_1286)
      | ~ v5_relat_1('#skF_3',A_1286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_16604])).

tff(c_21934,plain,(
    ! [B_65] :
      ( r1_tarski('#skF_2',B_65)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_243,c_21919])).

tff(c_21947,plain,(
    ! [B_65] : r1_tarski('#skF_2',B_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21806,c_21934])).

tff(c_22121,plain,(
    ! [B_1298,A_1299,C_1300] :
      ( k1_xboole_0 = B_1298
      | k1_relset_1(A_1299,B_1298,C_1300) = A_1299
      | ~ v1_funct_2(C_1300,A_1299,B_1298)
      | ~ m1_subset_1(C_1300,k1_zfmisc_1(k2_zfmisc_1(A_1299,B_1298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22130,plain,(
    ! [C_1300] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_1300) = '#skF_1'
      | ~ v1_funct_2(C_1300,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1300,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12548,c_22121])).

tff(c_22253,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22130])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12562,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12548,c_8])).

tff(c_12581,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12562])).

tff(c_21836,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_21806,c_2])).

tff(c_21846,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_12581,c_21836])).

tff(c_22264,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22253,c_21846])).

tff(c_22299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21947,c_22264])).

tff(c_23521,plain,(
    ! [C_1363] :
      ( k1_relset_1('#skF_1','#skF_2',C_1363) = '#skF_1'
      | ~ v1_funct_2(C_1363,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1363,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_22130])).

tff(c_23524,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_12551,c_23521])).

tff(c_23531,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16463,c_23524])).

tff(c_25958,plain,(
    ! [A_1426] :
      ( v5_relat_1(k2_funct_1(A_1426),k1_relat_1(A_1426))
      | ~ v1_relat_1(k2_funct_1(A_1426))
      | ~ v2_funct_1(A_1426)
      | ~ v1_funct_1(A_1426)
      | ~ v1_relat_1(A_1426) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12684,c_12602])).

tff(c_25966,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23531,c_25958])).

tff(c_25974,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_25966])).

tff(c_25975,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_25974])).

tff(c_25978,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_25975])).

tff(c_25982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_25978])).

tff(c_25984,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_25974])).

tff(c_25983,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_25974])).

tff(c_24827,plain,(
    ! [A_1404,A_1405] :
      ( r1_tarski(k1_relat_1(A_1404),A_1405)
      | ~ v5_relat_1(k2_funct_1(A_1404),A_1405)
      | ~ v1_relat_1(k2_funct_1(A_1404))
      | ~ v2_funct_1(A_1404)
      | ~ v1_funct_1(A_1404)
      | ~ v1_relat_1(A_1404) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12684,c_22])).

tff(c_26399,plain,(
    ! [A_1434] :
      ( r1_tarski(k1_relat_1(A_1434),k2_relat_1(k2_funct_1(A_1434)))
      | ~ v2_funct_1(A_1434)
      | ~ v1_funct_1(A_1434)
      | ~ v1_relat_1(A_1434)
      | ~ v1_relat_1(k2_funct_1(A_1434)) ) ),
    inference(resolution,[status(thm)],[c_12602,c_24827])).

tff(c_26410,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23531,c_26399])).

tff(c_26421,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25984,c_152,c_70,c_64,c_26410])).

tff(c_26425,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26421,c_237])).

tff(c_26436,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25984,c_25983,c_26425])).

tff(c_26729,plain,(
    ! [A_1437] :
      ( m1_subset_1(k2_funct_1(A_1437),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1437),k2_relat_1(k2_funct_1(A_1437)))))
      | ~ v1_funct_1(k2_funct_1(A_1437))
      | ~ v1_relat_1(k2_funct_1(A_1437))
      | ~ v2_funct_1(A_1437)
      | ~ v1_funct_1(A_1437)
      | ~ v1_relat_1(A_1437) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_16134])).

tff(c_26759,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26436,c_26729])).

tff(c_26812,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_25984,c_162,c_16567,c_26759])).

tff(c_26814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_26812])).

tff(c_26816,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12562])).

tff(c_26824,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26816,c_26816,c_12])).

tff(c_26815,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12562])).

tff(c_26830,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26816,c_26816,c_26815])).

tff(c_26831,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_26830])).

tff(c_26834,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26831,c_213])).

tff(c_26900,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26824,c_26834])).

tff(c_26822,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26816,c_26816,c_10])).

tff(c_27269,plain,(
    ! [A_1496,B_1497,C_1498] :
      ( k2_relset_1(A_1496,B_1497,C_1498) = k2_relat_1(C_1498)
      | ~ m1_subset_1(C_1498,k1_zfmisc_1(k2_zfmisc_1(A_1496,B_1497))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_27360,plain,(
    ! [A_1512,C_1513] :
      ( k2_relset_1(A_1512,'#skF_3',C_1513) = k2_relat_1(C_1513)
      | ~ m1_subset_1(C_1513,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26822,c_27269])).

tff(c_27377,plain,(
    ! [A_1516] : k2_relset_1(A_1516,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12551,c_27360])).

tff(c_26836,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26831,c_26831,c_62])).

tff(c_27384,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_27377,c_26836])).

tff(c_27004,plain,(
    ! [A_1466] :
      ( k1_relat_1(k2_funct_1(A_1466)) = k2_relat_1(A_1466)
      | ~ v2_funct_1(A_1466)
      | ~ v1_funct_1(A_1466)
      | ~ v1_relat_1(A_1466) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    ! [A_28] :
      ( v1_funct_2(A_28,k1_relat_1(A_28),k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30113,plain,(
    ! [A_1629] :
      ( v1_funct_2(k2_funct_1(A_1629),k2_relat_1(A_1629),k2_relat_1(k2_funct_1(A_1629)))
      | ~ v1_funct_1(k2_funct_1(A_1629))
      | ~ v1_relat_1(k2_funct_1(A_1629))
      | ~ v2_funct_1(A_1629)
      | ~ v1_funct_1(A_1629)
      | ~ v1_relat_1(A_1629) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27004,c_56])).

tff(c_30134,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_27384,c_30113])).

tff(c_30144,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_162,c_30134])).

tff(c_30245,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30144])).

tff(c_30248,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_30245])).

tff(c_30252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_30248])).

tff(c_30254,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_30144])).

tff(c_27088,plain,(
    ! [A_1475] :
      ( m1_subset_1(A_1475,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1475),k2_relat_1(A_1475))))
      | ~ v1_funct_1(A_1475)
      | ~ v1_relat_1(A_1475) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30320,plain,(
    ! [A_1634] :
      ( m1_subset_1(k2_funct_1(A_1634),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1634),k2_relat_1(k2_funct_1(A_1634)))))
      | ~ v1_funct_1(k2_funct_1(A_1634))
      | ~ v1_relat_1(k2_funct_1(A_1634))
      | ~ v2_funct_1(A_1634)
      | ~ v1_funct_1(A_1634)
      | ~ v1_relat_1(A_1634) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_27088])).

tff(c_30365,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_27384,c_30320])).

tff(c_30390,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_30254,c_162,c_26824,c_30365])).

tff(c_30392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26900,c_30390])).

tff(c_30393,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26830])).

tff(c_30458,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_30393,c_26822])).

tff(c_30399,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_213])).

tff(c_30518,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30458,c_30399])).

tff(c_30403,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_152])).

tff(c_30407,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_70])).

tff(c_30406,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_64])).

tff(c_30394,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26830])).

tff(c_30412,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_30394])).

tff(c_30440,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_30393,c_26824])).

tff(c_30396,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_30393,c_12551])).

tff(c_30896,plain,(
    ! [A_1698,B_1699,C_1700] :
      ( k1_relset_1(A_1698,B_1699,C_1700) = k1_relat_1(C_1700)
      | ~ m1_subset_1(C_1700,k1_zfmisc_1(k2_zfmisc_1(A_1698,B_1699))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_31392,plain,(
    ! [B_1733,C_1734] :
      ( k1_relset_1('#skF_1',B_1733,C_1734) = k1_relat_1(C_1734)
      | ~ m1_subset_1(C_1734,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30440,c_30896])).

tff(c_31401,plain,(
    ! [B_1735] : k1_relset_1('#skF_1',B_1735,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30396,c_31392])).

tff(c_30405,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_68])).

tff(c_30395,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_26816])).

tff(c_50,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_xboole_0
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_71,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_xboole_0
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_31293,plain,(
    ! [B_1721,C_1722] :
      ( k1_relset_1('#skF_1',B_1721,C_1722) = '#skF_1'
      | ~ v1_funct_2(C_1722,'#skF_1',B_1721)
      | ~ m1_subset_1(C_1722,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30395,c_30395,c_30395,c_30395,c_71])).

tff(c_31300,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30405,c_31293])).

tff(c_31310,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30396,c_31300])).

tff(c_31408,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_31401,c_31310])).

tff(c_30736,plain,(
    ! [A_1679,B_1680,C_1681] :
      ( k2_relset_1(A_1679,B_1680,C_1681) = k2_relat_1(C_1681)
      | ~ m1_subset_1(C_1681,k1_zfmisc_1(k2_zfmisc_1(A_1679,B_1680))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30818,plain,(
    ! [B_1694,C_1695] :
      ( k2_relset_1('#skF_1',B_1694,C_1695) = k2_relat_1(C_1695)
      | ~ m1_subset_1(C_1695,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30440,c_30736])).

tff(c_30826,plain,(
    ! [B_1696] : k2_relset_1('#skF_1',B_1696,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30396,c_30818])).

tff(c_30404,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_62])).

tff(c_30833,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_30826,c_30404])).

tff(c_54,plain,(
    ! [A_28] :
      ( m1_subset_1(A_28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_28),k2_relat_1(A_28))))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30852,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2')))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30833,c_54])).

tff(c_30877,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30403,c_30407,c_30852])).

tff(c_31041,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_30877,c_14])).

tff(c_31067,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2') = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_31041,c_2])).

tff(c_31330,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_31067])).

tff(c_31422,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31408,c_31330])).

tff(c_31430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_30440,c_31422])).

tff(c_31431,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_1'),'#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_31067])).

tff(c_26821,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_3'
      | A_3 = '#skF_3'
      | k2_zfmisc_1(A_3,B_4) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26816,c_26816,c_26816,c_8])).

tff(c_30612,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_1'
      | A_3 = '#skF_1'
      | k2_zfmisc_1(A_3,B_4) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_30393,c_30393,c_26821])).

tff(c_31459,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_31431,c_30612])).

tff(c_31489,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_30412,c_31459])).

tff(c_30672,plain,(
    ! [A_1671] :
      ( k2_relat_1(k2_funct_1(A_1671)) = k1_relat_1(A_1671)
      | ~ v2_funct_1(A_1671)
      | ~ v1_funct_1(A_1671)
      | ~ v1_relat_1(A_1671) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32616,plain,(
    ! [A_1805,A_1806] :
      ( v5_relat_1(k2_funct_1(A_1805),A_1806)
      | ~ r1_tarski(k1_relat_1(A_1805),A_1806)
      | ~ v1_relat_1(k2_funct_1(A_1805))
      | ~ v2_funct_1(A_1805)
      | ~ v1_funct_1(A_1805)
      | ~ v1_relat_1(A_1805) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30672,c_20])).

tff(c_187,plain,(
    ! [C_48,B_4] :
      ( v5_relat_1(C_48,B_4)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_174])).

tff(c_26818,plain,(
    ! [C_48,B_4] :
      ( v5_relat_1(C_48,B_4)
      | ~ m1_subset_1(C_48,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26816,c_187])).

tff(c_30508,plain,(
    ! [C_1645,B_1646] :
      ( v5_relat_1(C_1645,B_1646)
      | ~ m1_subset_1(C_1645,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_26818])).

tff(c_30514,plain,(
    ! [B_1646] : v5_relat_1('#skF_1',B_1646) ),
    inference(resolution,[status(thm)],[c_30396,c_30508])).

tff(c_30873,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_2',A_10)
      | ~ v5_relat_1('#skF_1',A_10)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30833,c_22])).

tff(c_30913,plain,(
    ! [A_1701] : r1_tarski('#skF_2',A_1701) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30403,c_30514,c_30873])).

tff(c_30975,plain,(
    ! [A_1706] :
      ( A_1706 = '#skF_2'
      | ~ r1_tarski(A_1706,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30913,c_2])).

tff(c_30990,plain,(
    ! [B_11] :
      ( k2_relat_1(B_11) = '#skF_2'
      | ~ v5_relat_1(B_11,'#skF_2')
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_30975])).

tff(c_32753,plain,(
    ! [A_1813] :
      ( k2_relat_1(k2_funct_1(A_1813)) = '#skF_2'
      | ~ r1_tarski(k1_relat_1(A_1813),'#skF_2')
      | ~ v1_relat_1(k2_funct_1(A_1813))
      | ~ v2_funct_1(A_1813)
      | ~ v1_funct_1(A_1813)
      | ~ v1_relat_1(A_1813) ) ),
    inference(resolution,[status(thm)],[c_32616,c_30990])).

tff(c_32756,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31489,c_32753])).

tff(c_32761,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30403,c_30407,c_30406,c_32756])).

tff(c_32762,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_32761])).

tff(c_32765,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_32762])).

tff(c_32769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30403,c_30407,c_32765])).

tff(c_32771,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_32761])).

tff(c_30402,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30393,c_162])).

tff(c_30775,plain,(
    ! [A_1690] :
      ( m1_subset_1(A_1690,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1690),k2_relat_1(A_1690))))
      | ~ v1_funct_1(A_1690)
      | ~ v1_relat_1(A_1690) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_33797,plain,(
    ! [A_1827] :
      ( m1_subset_1(k2_funct_1(A_1827),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1827)),k1_relat_1(A_1827))))
      | ~ v1_funct_1(k2_funct_1(A_1827))
      | ~ v1_relat_1(k2_funct_1(A_1827))
      | ~ v2_funct_1(A_1827)
      | ~ v1_funct_1(A_1827)
      | ~ v1_relat_1(A_1827) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_30775])).

tff(c_33824,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_31489,c_33797])).

tff(c_33842,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30403,c_30407,c_30406,c_32771,c_30402,c_30458,c_33824])).

tff(c_33844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30518,c_33842])).

tff(c_33845,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_36129,plain,(
    ! [A_2031,B_2032,C_2033] :
      ( k2_relset_1(A_2031,B_2032,C_2033) = k2_relat_1(C_2033)
      | ~ m1_subset_1(C_2033,k1_zfmisc_1(k2_zfmisc_1(A_2031,B_2032))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36142,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_36129])).

tff(c_36153,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36142])).

tff(c_33846,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_36022,plain,(
    ! [A_2018,B_2019,C_2020] :
      ( k1_relset_1(A_2018,B_2019,C_2020) = k1_relat_1(C_2020)
      | ~ m1_subset_1(C_2020,k1_zfmisc_1(k2_zfmisc_1(A_2018,B_2019))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36039,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_33846,c_36022])).

tff(c_36387,plain,(
    ! [B_2052,C_2053,A_2054] :
      ( k1_xboole_0 = B_2052
      | v1_funct_2(C_2053,A_2054,B_2052)
      | k1_relset_1(A_2054,B_2052,C_2053) != A_2054
      | ~ m1_subset_1(C_2053,k1_zfmisc_1(k2_zfmisc_1(A_2054,B_2052))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36396,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_33846,c_36387])).

tff(c_36415,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36039,c_36396])).

tff(c_36416,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_33845,c_36415])).

tff(c_36421,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36416])).

tff(c_36424,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_36421])).

tff(c_36427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_36153,c_36424])).

tff(c_36428,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36416])).

tff(c_33896,plain,(
    ! [C_1837,B_1838] :
      ( v5_relat_1(C_1837,B_1838)
      | ~ m1_subset_1(C_1837,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_174])).

tff(c_33900,plain,(
    ! [A_5,B_1838] :
      ( v5_relat_1(A_5,B_1838)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_33896])).

tff(c_36174,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_2',A_10)
      | ~ v5_relat_1('#skF_3',A_10)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36153,c_22])).

tff(c_36200,plain,(
    ! [A_2034] :
      ( r1_tarski('#skF_2',A_2034)
      | ~ v5_relat_1('#skF_3',A_2034) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_36174])).

tff(c_36212,plain,(
    ! [B_1838] :
      ( r1_tarski('#skF_2',B_1838)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_33900,c_36200])).

tff(c_36234,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_36212])).

tff(c_36442,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36428,c_36234])).

tff(c_36464,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36428,c_36428,c_12])).

tff(c_36581,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36464,c_113])).

tff(c_36584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36442,c_36581])).

tff(c_36585,plain,(
    ! [B_1838] : r1_tarski('#skF_2',B_1838) ),
    inference(splitRight,[status(thm)],[c_36212])).

tff(c_36041,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_36022])).

tff(c_37034,plain,(
    ! [B_2076,A_2077,C_2078] :
      ( k1_xboole_0 = B_2076
      | k1_relset_1(A_2077,B_2076,C_2078) = A_2077
      | ~ v1_funct_2(C_2078,A_2077,B_2076)
      | ~ m1_subset_1(C_2078,k1_zfmisc_1(k2_zfmisc_1(A_2077,B_2076))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_37050,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_37034])).

tff(c_37066,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_36041,c_37050])).

tff(c_37068,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_37066])).

tff(c_18,plain,(
    ! [B_9,A_7] :
      ( v1_relat_1(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_33855,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_33846,c_18])).

tff(c_33863,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_33855])).

tff(c_37174,plain,(
    ! [B_2084,C_2085,A_2086] :
      ( k1_xboole_0 = B_2084
      | v1_funct_2(C_2085,A_2086,B_2084)
      | k1_relset_1(A_2086,B_2084,C_2085) != A_2086
      | ~ m1_subset_1(C_2085,k1_zfmisc_1(k2_zfmisc_1(A_2086,B_2084))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_37180,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_33846,c_37174])).

tff(c_37196,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36039,c_37180])).

tff(c_37197,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_33845,c_37196])).

tff(c_37203,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_37197])).

tff(c_37206,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_37203])).

tff(c_37209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_36153,c_37206])).

tff(c_37210,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_37197])).

tff(c_37239,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37210,c_37210,c_10])).

tff(c_37421,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37239,c_33846])).

tff(c_37566,plain,(
    ! [C_2104,B_2105] :
      ( v5_relat_1(C_2104,B_2105)
      | ~ m1_subset_1(C_2104,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37210,c_187])).

tff(c_37583,plain,(
    ! [B_2106] : v5_relat_1(k2_funct_1('#skF_3'),B_2106) ),
    inference(resolution,[status(thm)],[c_37421,c_37566])).

tff(c_36590,plain,(
    ! [B_2060] : r1_tarski('#skF_2',B_2060) ),
    inference(splitRight,[status(thm)],[c_36212])).

tff(c_36665,plain,(
    ! [B_2067] :
      ( B_2067 = '#skF_2'
      | ~ r1_tarski(B_2067,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36590,c_2])).

tff(c_36680,plain,(
    ! [B_11] :
      ( k2_relat_1(B_11) = '#skF_2'
      | ~ v5_relat_1(B_11,'#skF_2')
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_36665])).

tff(c_37587,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_37583,c_36680])).

tff(c_37595,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33863,c_37587])).

tff(c_37622,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37595,c_30])).

tff(c_37643,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_37068,c_37622])).

tff(c_37669,plain,(
    ! [B_1838] : r1_tarski('#skF_1',B_1838) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37643,c_36585])).

tff(c_33864,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_33846,c_14])).

tff(c_33874,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_33864,c_2])).

tff(c_33894,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_33874])).

tff(c_37419,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37239,c_33894])).

tff(c_37720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37669,c_37419])).

tff(c_37721,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_37066])).

tff(c_36586,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_36212])).

tff(c_36617,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_36586,c_2])).

tff(c_36657,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36617])).

tff(c_37728,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37721,c_36657])).

tff(c_37751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36585,c_37728])).

tff(c_37752,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36617])).

tff(c_48,plain,(
    ! [B_26,C_27,A_25] :
      ( k1_xboole_0 = B_26
      | v1_funct_2(C_27,A_25,B_26)
      | k1_relset_1(A_25,B_26,C_27) != A_25
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38186,plain,(
    ! [B_2137,C_2138,A_2139] :
      ( B_2137 = '#skF_3'
      | v1_funct_2(C_2138,A_2139,B_2137)
      | k1_relset_1(A_2139,B_2137,C_2138) != A_2139
      | ~ m1_subset_1(C_2138,k1_zfmisc_1(k2_zfmisc_1(A_2139,B_2137))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37752,c_48])).

tff(c_38198,plain,
    ( '#skF_3' = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_33846,c_38186])).

tff(c_38209,plain,
    ( '#skF_3' = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36039,c_38198])).

tff(c_38210,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_33845,c_38209])).

tff(c_38300,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_38210])).

tff(c_38303,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_38300])).

tff(c_38306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_36153,c_38303])).

tff(c_38307,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_38210])).

tff(c_37775,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37752,c_37752,c_12])).

tff(c_38325,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38307,c_38307,c_37775])).

tff(c_33865,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_38336,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38307,c_33865])).

tff(c_38628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_38325,c_38336])).

tff(c_38629,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_33874])).

tff(c_38632,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38629,c_33846])).

tff(c_43094,plain,(
    ! [A_2517,B_2518,C_2519] :
      ( k1_relset_1(A_2517,B_2518,C_2519) = k1_relat_1(C_2519)
      | ~ m1_subset_1(C_2519,k1_zfmisc_1(k2_zfmisc_1(A_2517,B_2518))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_43125,plain,(
    ! [C_2522] :
      ( k1_relset_1('#skF_2','#skF_1',C_2522) = k1_relat_1(C_2522)
      | ~ m1_subset_1(C_2522,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38629,c_43094])).

tff(c_43133,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38632,c_43125])).

tff(c_44968,plain,(
    ! [B_2641,C_2642,A_2643] :
      ( k1_xboole_0 = B_2641
      | v1_funct_2(C_2642,A_2643,B_2641)
      | k1_relset_1(A_2643,B_2641,C_2642) != A_2643
      | ~ m1_subset_1(C_2642,k1_zfmisc_1(k2_zfmisc_1(A_2643,B_2641))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44977,plain,(
    ! [C_2642] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_2642,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_2642) != '#skF_2'
      | ~ m1_subset_1(C_2642,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38629,c_44968])).

tff(c_45046,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_44977])).

tff(c_38643,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38629,c_8])).

tff(c_38681,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38643])).

tff(c_45073,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45046,c_38681])).

tff(c_45079,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45046,c_45046,c_10])).

tff(c_45309,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45079,c_38629])).

tff(c_45311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45073,c_45309])).

tff(c_46028,plain,(
    ! [C_2711] :
      ( v1_funct_2(C_2711,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_2711) != '#skF_2'
      | ~ m1_subset_1(C_2711,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_44977])).

tff(c_46031,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_38632,c_46028])).

tff(c_46037,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43133,c_46031])).

tff(c_46038,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_33845,c_46037])).

tff(c_46042,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_46038])).

tff(c_46045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_43198,c_46042])).

tff(c_46046,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_38643])).

tff(c_46110,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_46046])).

tff(c_42,plain,(
    ! [A_25] :
      ( v1_funct_2(k1_xboole_0,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_25,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_74,plain,(
    ! [A_25] :
      ( v1_funct_2(k1_xboole_0,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_46130,plain,(
    ! [A_25] :
      ( v1_funct_2('#skF_1',A_25,'#skF_1')
      | A_25 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46110,c_46110,c_46110,c_46110,c_46110,c_74])).

tff(c_46131,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_46130])).

tff(c_46219,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_46131])).

tff(c_46223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_46219])).

tff(c_46225,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46130])).

tff(c_46,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_72,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_46771,plain,(
    ! [C_2757,B_2758] :
      ( v1_funct_2(C_2757,'#skF_1',B_2758)
      | k1_relset_1('#skF_1',B_2758,C_2757) != '#skF_1'
      | ~ m1_subset_1(C_2757,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46110,c_46110,c_46110,c_46110,c_72])).

tff(c_46937,plain,(
    ! [B_2771] :
      ( v1_funct_2('#skF_1','#skF_1',B_2771)
      | k1_relset_1('#skF_1',B_2771,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_46225,c_46771])).

tff(c_46443,plain,(
    ! [A_2728] :
      ( v1_funct_2('#skF_1',A_2728,'#skF_1')
      | A_2728 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_46130])).

tff(c_46047,plain,(
    k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38643])).

tff(c_46053,plain,(
    ~ v1_funct_2(k1_xboole_0,'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46047,c_33845])).

tff(c_46115,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46110,c_46053])).

tff(c_46447,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46443,c_46115])).

tff(c_46448,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46447,c_46115])).

tff(c_46953,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_46937,c_46448])).

tff(c_46117,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46110,c_46047])).

tff(c_46377,plain,(
    ! [A_2726] :
      ( k1_relat_1(k2_funct_1(A_2726)) = k2_relat_1(A_2726)
      | ~ v2_funct_1(A_2726)
      | ~ v1_funct_1(A_2726)
      | ~ v1_relat_1(A_2726) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46389,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46117,c_46377])).

tff(c_46393,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_46389])).

tff(c_46125,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46110,c_46110,c_12])).

tff(c_46255,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46125,c_66])).

tff(c_46123,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46110,c_46110,c_10])).

tff(c_46456,plain,(
    ! [A_2729,B_2730,C_2731] :
      ( k2_relset_1(A_2729,B_2730,C_2731) = k2_relat_1(C_2731)
      | ~ m1_subset_1(C_2731,k1_zfmisc_1(k2_zfmisc_1(A_2729,B_2730))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_47211,plain,(
    ! [A_2787,C_2788] :
      ( k2_relset_1(A_2787,'#skF_1',C_2788) = k2_relat_1(C_2788)
      | ~ m1_subset_1(C_2788,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46123,c_46456])).

tff(c_47213,plain,(
    ! [A_2787] : k2_relset_1(A_2787,'#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46255,c_47211])).

tff(c_47224,plain,(
    ! [A_2789] : k2_relset_1(A_2789,'#skF_1','#skF_3') = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46393,c_47213])).

tff(c_46450,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46447,c_46447,c_62])).

tff(c_47228,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_47224,c_46450])).

tff(c_78,plain,(
    ! [B_32] : k2_zfmisc_1(k1_xboole_0,B_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_24])).

tff(c_46124,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46110,c_82])).

tff(c_46048,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46047,c_46047,c_38632])).

tff(c_46099,plain,(
    ! [B_4] : v5_relat_1(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_46048,c_187])).

tff(c_46112,plain,(
    ! [B_4] : v5_relat_1('#skF_1',B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46110,c_46099])).

tff(c_46281,plain,(
    ! [A_2723] :
      ( k2_relat_1(k2_funct_1(A_2723)) = k1_relat_1(A_2723)
      | ~ v2_funct_1(A_2723)
      | ~ v1_funct_1(A_2723)
      | ~ v1_relat_1(A_2723) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46302,plain,
    ( k2_relat_1('#skF_1') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46117,c_46281])).

tff(c_46306,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_46302])).

tff(c_46351,plain,(
    ! [A_10] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_10)
      | ~ v5_relat_1('#skF_1',A_10)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46306,c_22])).

tff(c_46363,plain,(
    ! [A_10] : r1_tarski(k1_relat_1('#skF_3'),A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46124,c_46112,c_46351])).

tff(c_46549,plain,(
    ! [C_2741,B_2742] :
      ( v5_relat_1(C_2741,B_2742)
      | ~ m1_subset_1(C_2741,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46110,c_187])).

tff(c_46557,plain,(
    ! [B_2742] : v5_relat_1('#skF_3',B_2742) ),
    inference(resolution,[status(thm)],[c_46255,c_46549])).

tff(c_46400,plain,(
    ! [A_10] :
      ( r1_tarski(k1_relat_1('#skF_1'),A_10)
      | ~ v5_relat_1('#skF_3',A_10)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46393,c_22])).

tff(c_46412,plain,(
    ! [A_10] :
      ( r1_tarski(k1_relat_1('#skF_1'),A_10)
      | ~ v5_relat_1('#skF_3',A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_46400])).

tff(c_46566,plain,(
    ! [A_2744] : r1_tarski(k1_relat_1('#skF_1'),A_2744) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46557,c_46412])).

tff(c_46603,plain,(
    ! [A_2748] :
      ( k1_relat_1('#skF_1') = A_2748
      | ~ r1_tarski(A_2748,k1_relat_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_46566,c_2])).

tff(c_46622,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_46363,c_46603])).

tff(c_46054,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46047,c_162])).

tff(c_46116,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46110,c_46054])).

tff(c_46496,plain,(
    ! [A_2737] :
      ( m1_subset_1(A_2737,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2737),k2_relat_1(A_2737))))
      | ~ v1_funct_1(A_2737)
      | ~ v1_relat_1(A_2737) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46520,plain,
    ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_46306,c_46496])).

tff(c_46534,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46124,c_46116,c_46520])).

tff(c_46847,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_relat_1('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46622,c_46534])).

tff(c_38,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_relset_1(A_19,B_20,C_21) = k1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46866,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'),'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_46847,c_38])).

tff(c_47241,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47228,c_47228,c_47228,c_46866])).

tff(c_47262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46953,c_47241])).

tff(c_47263,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_46046])).

tff(c_47264,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_46046])).

tff(c_47285,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47263,c_47264])).

tff(c_47278,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47263,c_47263,c_10])).

tff(c_47415,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47278,c_66])).

tff(c_44,plain,(
    ! [C_27,A_25] :
      ( k1_xboole_0 = C_27
      | ~ v1_funct_2(C_27,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_73,plain,(
    ! [C_27,A_25] :
      ( k1_xboole_0 = C_27
      | ~ v1_funct_2(C_27,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_47554,plain,(
    ! [C_2801,A_2802] :
      ( C_2801 = '#skF_2'
      | ~ v1_funct_2(C_2801,A_2802,'#skF_2')
      | A_2802 = '#skF_2'
      | ~ m1_subset_1(C_2801,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47263,c_47263,c_47263,c_47263,c_73])).

tff(c_47556,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_47554])).

tff(c_47559,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47415,c_47556])).

tff(c_47560,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_47285,c_47559])).

tff(c_47413,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47278,c_33865])).

tff(c_47569,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47560,c_47413])).

tff(c_47587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_47569])).

tff(c_47588,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_47591,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47588,c_66])).

tff(c_48795,plain,(
    ! [A_2924,B_2925,C_2926] :
      ( k2_relset_1(A_2924,B_2925,C_2926) = k2_relat_1(C_2926)
      | ~ m1_subset_1(C_2926,k1_zfmisc_1(k2_zfmisc_1(A_2924,B_2925))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48849,plain,(
    ! [C_2931] :
      ( k2_relset_1('#skF_1','#skF_2',C_2931) = k2_relat_1(C_2931)
      | ~ m1_subset_1(C_2931,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47588,c_48795])).

tff(c_48852,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_47591,c_48849])).

tff(c_48858,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_48852])).

tff(c_48921,plain,(
    ! [A_2933,B_2934,C_2935] :
      ( k1_relset_1(A_2933,B_2934,C_2935) = k1_relat_1(C_2935)
      | ~ m1_subset_1(C_2935,k1_zfmisc_1(k2_zfmisc_1(A_2933,B_2934))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48938,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_33846,c_48921])).

tff(c_49644,plain,(
    ! [B_3006,C_3007,A_3008] :
      ( k1_xboole_0 = B_3006
      | v1_funct_2(C_3007,A_3008,B_3006)
      | k1_relset_1(A_3008,B_3006,C_3007) != A_3008
      | ~ m1_subset_1(C_3007,k1_zfmisc_1(k2_zfmisc_1(A_3008,B_3006))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_49656,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_33846,c_49644])).

tff(c_49672,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48938,c_49656])).

tff(c_49673,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_33845,c_49672])).

tff(c_49676,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_49673])).

tff(c_49679,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_49676])).

tff(c_49682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_48858,c_49679])).

tff(c_49683,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_49673])).

tff(c_47602,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_47588,c_8])).

tff(c_47630,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_47602])).

tff(c_49727,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49683,c_47630])).

tff(c_49731,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49683,c_49683,c_12])).

tff(c_49811,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49731,c_47588])).

tff(c_49813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49727,c_49811])).

tff(c_49815,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_47602])).

tff(c_49942,plain,(
    ! [C_3026,B_3027] :
      ( v5_relat_1(C_3026,B_3027)
      | ~ m1_subset_1(C_3026,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49815,c_187])).

tff(c_49948,plain,(
    ! [B_3027] : v5_relat_1('#skF_3',B_3027) ),
    inference(resolution,[status(thm)],[c_47591,c_49942])).

tff(c_49819,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49815,c_49815,c_10])).

tff(c_50250,plain,(
    ! [A_3068,B_3069,C_3070] :
      ( k2_relset_1(A_3068,B_3069,C_3070) = k2_relat_1(C_3070)
      | ~ m1_subset_1(C_3070,k1_zfmisc_1(k2_zfmisc_1(A_3068,B_3069))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50274,plain,(
    ! [A_3075,C_3076] :
      ( k2_relset_1(A_3075,'#skF_3',C_3076) = k2_relat_1(C_3076)
      | ~ m1_subset_1(C_3076,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49819,c_50250])).

tff(c_50285,plain,(
    ! [A_3077] : k2_relset_1(A_3077,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_47591,c_50274])).

tff(c_49814,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_47602])).

tff(c_49827,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49815,c_49815,c_49814])).

tff(c_49828,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_49827])).

tff(c_49835,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49828,c_49828,c_62])).

tff(c_50289,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_50285,c_49835])).

tff(c_50341,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_3',A_10)
      | ~ v5_relat_1('#skF_3',A_10)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50289,c_22])).

tff(c_50359,plain,(
    ! [A_10] : r1_tarski('#skF_3',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_49948,c_50341])).

tff(c_49821,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49815,c_49815,c_12])).

tff(c_47629,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_33864,c_2])).

tff(c_49981,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49821,c_49828,c_49821,c_49828,c_47629])).

tff(c_49982,plain,(
    ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_49981])).

tff(c_50364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50359,c_49982])).

tff(c_50365,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_49981])).

tff(c_49829,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49828,c_33864])).

tff(c_49906,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49821,c_49829])).

tff(c_49915,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_49906,c_2])).

tff(c_49980,plain,(
    ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_49915])).

tff(c_50396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50365,c_49980])).

tff(c_50397,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_49915])).

tff(c_50427,plain,(
    ! [A_3081] :
      ( k1_relat_1(k2_funct_1(A_3081)) = k2_relat_1(A_3081)
      | ~ v2_funct_1(A_3081)
      | ~ v1_funct_1(A_3081)
      | ~ v1_relat_1(A_3081) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50439,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50397,c_50427])).

tff(c_50443,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70,c_64,c_50439])).

tff(c_50834,plain,(
    ! [A_3112,B_3113,C_3114] :
      ( k2_relset_1(A_3112,B_3113,C_3114) = k2_relat_1(C_3114)
      | ~ m1_subset_1(C_3114,k1_zfmisc_1(k2_zfmisc_1(A_3112,B_3113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50846,plain,(
    ! [A_3115,C_3116] :
      ( k2_relset_1(A_3115,'#skF_3',C_3116) = k2_relat_1(C_3116)
      | ~ m1_subset_1(C_3116,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49819,c_50834])).

tff(c_50848,plain,(
    ! [A_3115] : k2_relset_1(A_3115,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_47591,c_50846])).

tff(c_50855,plain,(
    ! [A_3117] : k2_relset_1(A_3117,'#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50443,c_50848])).

tff(c_50859,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_50855,c_49835])).

tff(c_50456,plain,(
    ! [A_10] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_10)
      | ~ v5_relat_1('#skF_3',A_10)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50443,c_22])).

tff(c_50466,plain,(
    ! [A_10] : r1_tarski(k1_relat_1('#skF_3'),A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_49948,c_50456])).

tff(c_50878,plain,(
    ! [A_10] : r1_tarski('#skF_3',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50859,c_50466])).

tff(c_50948,plain,(
    ! [A_3119,B_3120,C_3121] :
      ( k1_relset_1(A_3119,B_3120,C_3121) = k1_relat_1(C_3121)
      | ~ m1_subset_1(C_3121,k1_zfmisc_1(k2_zfmisc_1(A_3119,B_3120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_51284,plain,(
    ! [A_3149,B_3150,A_3151] :
      ( k1_relset_1(A_3149,B_3150,A_3151) = k1_relat_1(A_3151)
      | ~ r1_tarski(A_3151,k2_zfmisc_1(A_3149,B_3150)) ) ),
    inference(resolution,[status(thm)],[c_16,c_50948])).

tff(c_51291,plain,(
    ! [A_3149,B_3150] : k1_relset_1(A_3149,B_3150,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50878,c_51284])).

tff(c_51308,plain,(
    ! [A_3149,B_3150] : k1_relset_1(A_3149,B_3150,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50859,c_51291])).

tff(c_51338,plain,(
    ! [C_3156,B_3157] :
      ( v1_funct_2(C_3156,'#skF_3',B_3157)
      | k1_relset_1('#skF_3',B_3157,C_3156) != '#skF_3'
      | ~ m1_subset_1(C_3156,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49815,c_49815,c_49815,c_49815,c_72])).

tff(c_51340,plain,(
    ! [B_3157] :
      ( v1_funct_2('#skF_3','#skF_3',B_3157)
      | k1_relset_1('#skF_3',B_3157,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_47591,c_51338])).

tff(c_51346,plain,(
    ! [B_3157] : v1_funct_2('#skF_3','#skF_3',B_3157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51308,c_51340])).

tff(c_49833,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49828,c_33845])).

tff(c_50403,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50397,c_49833])).

tff(c_51351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51346,c_50403])).

tff(c_51352,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_49827])).

tff(c_51353,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_49827])).

tff(c_51375,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_51353])).

tff(c_51366,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_152])).

tff(c_51370,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_70])).

tff(c_51369,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_64])).

tff(c_51360,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_33863])).

tff(c_51386,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_51352,c_49819])).

tff(c_51361,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_33846])).

tff(c_51457,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51386,c_51361])).

tff(c_51354,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_49815])).

tff(c_51518,plain,(
    ! [C_3175,B_3176] :
      ( v5_relat_1(C_3175,B_3176)
      | ~ m1_subset_1(C_3175,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51354,c_187])).

tff(c_51526,plain,(
    ! [B_3176] : v5_relat_1(k2_funct_1('#skF_1'),B_3176) ),
    inference(resolution,[status(thm)],[c_51457,c_51518])).

tff(c_51356,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_51352,c_47591])).

tff(c_51527,plain,(
    ! [B_3176] : v5_relat_1('#skF_1',B_3176) ),
    inference(resolution,[status(thm)],[c_51356,c_51518])).

tff(c_51414,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_51352,c_49821])).

tff(c_51722,plain,(
    ! [A_3203,B_3204,C_3205] :
      ( k2_relset_1(A_3203,B_3204,C_3205) = k2_relat_1(C_3205)
      | ~ m1_subset_1(C_3205,k1_zfmisc_1(k2_zfmisc_1(A_3203,B_3204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_51738,plain,(
    ! [B_3207,C_3208] :
      ( k2_relset_1('#skF_1',B_3207,C_3208) = k2_relat_1(C_3208)
      | ~ m1_subset_1(C_3208,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51414,c_51722])).

tff(c_51749,plain,(
    ! [B_3209] : k2_relset_1('#skF_1',B_3209,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_51356,c_51738])).

tff(c_51367,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_62])).

tff(c_51753,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_51749,c_51367])).

tff(c_51774,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_2',A_10)
      | ~ v5_relat_1('#skF_1',A_10)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51753,c_22])).

tff(c_51793,plain,(
    ! [A_3210] : r1_tarski('#skF_2',A_3210) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51366,c_51527,c_51774])).

tff(c_51835,plain,(
    ! [A_3216] :
      ( A_3216 = '#skF_2'
      | ~ r1_tarski(A_3216,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_51793,c_2])).

tff(c_51875,plain,(
    ! [B_3218] :
      ( k2_relat_1(B_3218) = '#skF_2'
      | ~ v5_relat_1(B_3218,'#skF_2')
      | ~ v1_relat_1(B_3218) ) ),
    inference(resolution,[status(thm)],[c_22,c_51835])).

tff(c_51891,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_51526,c_51875])).

tff(c_51905,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51360,c_51891])).

tff(c_51961,plain,
    ( k1_relat_1('#skF_1') = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_51905,c_30])).

tff(c_51982,plain,(
    k1_relat_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51366,c_51370,c_51369,c_51961])).

tff(c_51909,plain,(
    ! [A_3219,B_3220,C_3221] :
      ( k1_relset_1(A_3219,B_3220,C_3221) = k1_relat_1(C_3221)
      | ~ m1_subset_1(C_3221,k1_zfmisc_1(k2_zfmisc_1(A_3219,B_3220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52423,plain,(
    ! [B_3237,C_3238] :
      ( k1_relset_1('#skF_1',B_3237,C_3238) = k1_relat_1(C_3238)
      | ~ m1_subset_1(C_3238,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51414,c_51909])).

tff(c_52427,plain,(
    ! [B_3237] : k1_relset_1('#skF_1',B_3237,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_51356,c_52423])).

tff(c_52436,plain,(
    ! [B_3239] : k1_relset_1('#skF_1',B_3239,'#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51982,c_52427])).

tff(c_51368,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51352,c_68])).

tff(c_52196,plain,(
    ! [B_3227,C_3228] :
      ( k1_relset_1('#skF_1',B_3227,C_3228) = '#skF_1'
      | ~ v1_funct_2(C_3228,'#skF_1',B_3227)
      | ~ m1_subset_1(C_3228,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51354,c_51354,c_51354,c_51354,c_71])).

tff(c_52201,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_51368,c_52196])).

tff(c_52208,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51356,c_52201])).

tff(c_52440,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_52436,c_52208])).

tff(c_52447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51375,c_52440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.22/6.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.70/6.82  
% 14.70/6.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.70/6.82  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 14.70/6.82  
% 14.70/6.82  %Foreground sorts:
% 14.70/6.82  
% 14.70/6.82  
% 14.70/6.82  %Background operators:
% 14.70/6.82  
% 14.70/6.82  
% 14.70/6.82  %Foreground operators:
% 14.70/6.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.70/6.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.70/6.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.70/6.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.70/6.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.70/6.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.70/6.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.70/6.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.70/6.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.70/6.82  tff('#skF_2', type, '#skF_2': $i).
% 14.70/6.82  tff('#skF_3', type, '#skF_3': $i).
% 14.70/6.82  tff('#skF_1', type, '#skF_1': $i).
% 14.70/6.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.70/6.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.70/6.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.70/6.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.70/6.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.70/6.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.70/6.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.70/6.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.70/6.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.70/6.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.70/6.82  
% 14.70/6.88  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 14.70/6.88  tff(f_133, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 14.70/6.88  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 14.70/6.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.70/6.88  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.70/6.88  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.70/6.88  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 14.70/6.88  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 14.70/6.88  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.70/6.88  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 14.70/6.88  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 14.70/6.88  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 14.70/6.88  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.70/6.88  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.70/6.88  tff(c_24, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.70/6.88  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.70/6.88  tff(c_142, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.70/6.88  tff(c_148, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_142])).
% 14.70/6.88  tff(c_152, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_148])).
% 14.70/6.88  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.70/6.88  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.70/6.88  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.70/6.88  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.70/6.88  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.70/6.88  tff(c_43179, plain, (![A_2529, B_2530, C_2531]: (k2_relset_1(A_2529, B_2530, C_2531)=k2_relat_1(C_2531) | ~m1_subset_1(C_2531, k1_zfmisc_1(k2_zfmisc_1(A_2529, B_2530))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.70/6.88  tff(c_43189, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_43179])).
% 14.70/6.88  tff(c_43198, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_43189])).
% 14.70/6.88  tff(c_32, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.70/6.88  tff(c_26, plain, (![A_14]: (v1_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.70/6.88  tff(c_60, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.70/6.88  tff(c_153, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 14.70/6.88  tff(c_156, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_153])).
% 14.70/6.88  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_156])).
% 14.70/6.88  tff(c_161, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_60])).
% 14.70/6.88  tff(c_213, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_161])).
% 14.70/6.88  tff(c_28, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.70/6.88  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.70/6.88  tff(c_217, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_213])).
% 14.70/6.88  tff(c_3875, plain, (![A_296, B_297, C_298]: (k2_relset_1(A_296, B_297, C_298)=k2_relat_1(C_298) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.70/6.88  tff(c_3885, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3875])).
% 14.70/6.88  tff(c_3895, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3885])).
% 14.70/6.88  tff(c_3837, plain, (![A_291, B_292, C_293]: (k1_relset_1(A_291, B_292, C_293)=k1_relat_1(C_293) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.70/6.88  tff(c_3856, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3837])).
% 14.70/6.88  tff(c_6578, plain, (![B_444, A_445, C_446]: (k1_xboole_0=B_444 | k1_relset_1(A_445, B_444, C_446)=A_445 | ~v1_funct_2(C_446, A_445, B_444) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_445, B_444))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.70/6.88  tff(c_6591, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_6578])).
% 14.70/6.88  tff(c_6605, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3856, c_6591])).
% 14.70/6.88  tff(c_6621, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_6605])).
% 14.70/6.88  tff(c_3607, plain, (![A_264]: (k2_relat_1(k2_funct_1(A_264))=k1_relat_1(A_264) | ~v2_funct_1(A_264) | ~v1_funct_1(A_264) | ~v1_relat_1(A_264))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.70/6.88  tff(c_277, plain, (![B_74, A_75]: (v5_relat_1(B_74, A_75) | ~r1_tarski(k2_relat_1(B_74), A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.70/6.88  tff(c_286, plain, (![B_74]: (v5_relat_1(B_74, k2_relat_1(B_74)) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_6, c_277])).
% 14.70/6.88  tff(c_7564, plain, (![A_535]: (v5_relat_1(k2_funct_1(A_535), k1_relat_1(A_535)) | ~v1_relat_1(k2_funct_1(A_535)) | ~v2_funct_1(A_535) | ~v1_funct_1(A_535) | ~v1_relat_1(A_535))), inference(superposition, [status(thm), theory('equality')], [c_3607, c_286])).
% 14.70/6.88  tff(c_7569, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6621, c_7564])).
% 14.70/6.88  tff(c_7575, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_7569])).
% 14.70/6.88  tff(c_7576, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7575])).
% 14.70/6.88  tff(c_7579, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_7576])).
% 14.70/6.88  tff(c_7583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_7579])).
% 14.70/6.88  tff(c_7585, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7575])).
% 14.70/6.88  tff(c_162, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 14.70/6.88  tff(c_7584, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_7575])).
% 14.70/6.88  tff(c_22, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.70/6.88  tff(c_7592, plain, (![A_536, A_537]: (r1_tarski(k1_relat_1(A_536), A_537) | ~v5_relat_1(k2_funct_1(A_536), A_537) | ~v1_relat_1(k2_funct_1(A_536)) | ~v2_funct_1(A_536) | ~v1_funct_1(A_536) | ~v1_relat_1(A_536))), inference(superposition, [status(thm), theory('equality')], [c_3607, c_22])).
% 14.70/6.88  tff(c_7731, plain, (![A_544]: (r1_tarski(k1_relat_1(A_544), k2_relat_1(k2_funct_1(A_544))) | ~v2_funct_1(A_544) | ~v1_funct_1(A_544) | ~v1_relat_1(A_544) | ~v1_relat_1(k2_funct_1(A_544)))), inference(resolution, [status(thm)], [c_286, c_7592])).
% 14.70/6.88  tff(c_7742, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6621, c_7731])).
% 14.70/6.88  tff(c_7753, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_7585, c_152, c_70, c_64, c_7742])).
% 14.70/6.88  tff(c_230, plain, (![B_60, A_61]: (r1_tarski(k2_relat_1(B_60), A_61) | ~v5_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.70/6.88  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.70/6.88  tff(c_237, plain, (![B_60, A_61]: (k2_relat_1(B_60)=A_61 | ~r1_tarski(A_61, k2_relat_1(B_60)) | ~v5_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_230, c_2])).
% 14.70/6.88  tff(c_7757, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7753, c_237])).
% 14.70/6.88  tff(c_7768, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7585, c_7584, c_7757])).
% 14.70/6.88  tff(c_3735, plain, (![A_282]: (m1_subset_1(A_282, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_282), k2_relat_1(A_282)))) | ~v1_funct_1(A_282) | ~v1_relat_1(A_282))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.70/6.88  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.70/6.88  tff(c_3759, plain, (![A_282]: (r1_tarski(A_282, k2_zfmisc_1(k1_relat_1(A_282), k2_relat_1(A_282))) | ~v1_funct_1(A_282) | ~v1_relat_1(A_282))), inference(resolution, [status(thm)], [c_3735, c_14])).
% 14.70/6.88  tff(c_7836, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7768, c_3759])).
% 14.70/6.88  tff(c_7906, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7585, c_162, c_7836])).
% 14.70/6.88  tff(c_8078, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_7906])).
% 14.70/6.88  tff(c_8095, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_3895, c_8078])).
% 14.70/6.88  tff(c_8097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_8095])).
% 14.70/6.88  tff(c_8098, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_6605])).
% 14.70/6.88  tff(c_4249, plain, (![B_325, A_326, C_327]: (k1_xboole_0=B_325 | k1_relset_1(A_326, B_325, C_327)=A_326 | ~v1_funct_2(C_327, A_326, B_325) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_326, B_325))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.70/6.88  tff(c_4262, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_4249])).
% 14.70/6.88  tff(c_4276, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3856, c_4262])).
% 14.70/6.88  tff(c_4278, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_4276])).
% 14.70/6.88  tff(c_4994, plain, (![A_394]: (v5_relat_1(k2_funct_1(A_394), k1_relat_1(A_394)) | ~v1_relat_1(k2_funct_1(A_394)) | ~v2_funct_1(A_394) | ~v1_funct_1(A_394) | ~v1_relat_1(A_394))), inference(superposition, [status(thm), theory('equality')], [c_3607, c_286])).
% 14.70/6.88  tff(c_4999, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4278, c_4994])).
% 14.70/6.88  tff(c_5005, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_4999])).
% 14.70/6.88  tff(c_5006, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5005])).
% 14.70/6.88  tff(c_5009, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_5006])).
% 14.70/6.88  tff(c_5013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_5009])).
% 14.70/6.88  tff(c_5015, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5005])).
% 14.70/6.88  tff(c_5014, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_5005])).
% 14.70/6.88  tff(c_5041, plain, (![A_395, A_396]: (r1_tarski(k1_relat_1(A_395), A_396) | ~v5_relat_1(k2_funct_1(A_395), A_396) | ~v1_relat_1(k2_funct_1(A_395)) | ~v2_funct_1(A_395) | ~v1_funct_1(A_395) | ~v1_relat_1(A_395))), inference(superposition, [status(thm), theory('equality')], [c_3607, c_22])).
% 14.70/6.88  tff(c_5906, plain, (![A_430]: (r1_tarski(k1_relat_1(A_430), k2_relat_1(k2_funct_1(A_430))) | ~v2_funct_1(A_430) | ~v1_funct_1(A_430) | ~v1_relat_1(A_430) | ~v1_relat_1(k2_funct_1(A_430)))), inference(resolution, [status(thm)], [c_286, c_5041])).
% 14.70/6.88  tff(c_5917, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4278, c_5906])).
% 14.70/6.88  tff(c_5928, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5015, c_152, c_70, c_64, c_5917])).
% 14.70/6.88  tff(c_5932, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5928, c_237])).
% 14.70/6.88  tff(c_5943, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5015, c_5014, c_5932])).
% 14.70/6.88  tff(c_6298, plain, (![A_431]: (m1_subset_1(k2_funct_1(A_431), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_431), k2_relat_1(k2_funct_1(A_431))))) | ~v1_funct_1(k2_funct_1(A_431)) | ~v1_relat_1(k2_funct_1(A_431)) | ~v2_funct_1(A_431) | ~v1_funct_1(A_431) | ~v1_relat_1(A_431))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3735])).
% 14.70/6.88  tff(c_6328, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5943, c_6298])).
% 14.70/6.88  tff(c_6351, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_5015, c_162, c_3895, c_6328])).
% 14.70/6.88  tff(c_6353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_213, c_6351])).
% 14.70/6.88  tff(c_6354, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4276])).
% 14.70/6.88  tff(c_20, plain, (![B_11, A_10]: (v5_relat_1(B_11, A_10) | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.70/6.88  tff(c_3922, plain, (![A_10]: (v5_relat_1('#skF_3', A_10) | ~r1_tarski('#skF_2', A_10) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3895, c_20])).
% 14.70/6.88  tff(c_3943, plain, (![A_10]: (v5_relat_1('#skF_3', A_10) | ~r1_tarski('#skF_2', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_3922])).
% 14.70/6.88  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.70/6.88  tff(c_190, plain, (![C_51, A_52, B_53]: (v4_relat_1(C_51, A_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.70/6.88  tff(c_288, plain, (![A_77, A_78, B_79]: (v4_relat_1(A_77, A_78) | ~r1_tarski(A_77, k2_zfmisc_1(A_78, B_79)))), inference(resolution, [status(thm)], [c_16, c_190])).
% 14.70/6.88  tff(c_3680, plain, (![B_270, A_271, B_272]: (v4_relat_1(k2_relat_1(B_270), A_271) | ~v5_relat_1(B_270, k2_zfmisc_1(A_271, B_272)) | ~v1_relat_1(B_270))), inference(resolution, [status(thm)], [c_22, c_288])).
% 14.70/6.88  tff(c_3695, plain, (![B_270, A_3]: (v4_relat_1(k2_relat_1(B_270), A_3) | ~v5_relat_1(B_270, k1_xboole_0) | ~v1_relat_1(B_270))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3680])).
% 14.70/6.88  tff(c_3910, plain, (![A_3]: (v4_relat_1('#skF_2', A_3) | ~v5_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3895, c_3695])).
% 14.70/6.88  tff(c_3935, plain, (![A_3]: (v4_relat_1('#skF_2', A_3) | ~v5_relat_1('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_3910])).
% 14.70/6.88  tff(c_4015, plain, (~v5_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3935])).
% 14.70/6.88  tff(c_4022, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_3943, c_4015])).
% 14.70/6.88  tff(c_6368, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6354, c_4022])).
% 14.70/6.88  tff(c_6395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6368])).
% 14.70/6.88  tff(c_6397, plain, (v5_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3935])).
% 14.70/6.88  tff(c_3925, plain, (![A_10]: (r1_tarski('#skF_2', A_10) | ~v5_relat_1('#skF_3', A_10) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3895, c_22])).
% 14.70/6.88  tff(c_3945, plain, (![A_10]: (r1_tarski('#skF_2', A_10) | ~v5_relat_1('#skF_3', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_3925])).
% 14.70/6.88  tff(c_6404, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_6397, c_3945])).
% 14.70/6.88  tff(c_6417, plain, (k1_xboole_0='#skF_2' | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_6404, c_2])).
% 14.70/6.88  tff(c_6418, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_6417])).
% 14.70/6.88  tff(c_8106, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8098, c_6418])).
% 14.70/6.88  tff(c_8134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8106])).
% 14.70/6.88  tff(c_8135, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_6417])).
% 14.70/6.88  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.70/6.88  tff(c_174, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 14.70/6.88  tff(c_239, plain, (![C_64, B_65]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_174])).
% 14.70/6.88  tff(c_243, plain, (![A_5, B_65]: (v5_relat_1(A_5, B_65) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_239])).
% 14.70/6.88  tff(c_3992, plain, (![A_302]: (r1_tarski('#skF_2', A_302) | ~v5_relat_1('#skF_3', A_302))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_3925])).
% 14.70/6.88  tff(c_4011, plain, (![B_65]: (r1_tarski('#skF_2', B_65) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_243, c_3992])).
% 14.70/6.88  tff(c_4014, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4011])).
% 14.70/6.88  tff(c_8139, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8135, c_4014])).
% 14.70/6.88  tff(c_8159, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8135, c_8135, c_10])).
% 14.70/6.88  tff(c_3901, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3895, c_3759])).
% 14.70/6.88  tff(c_3929, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_3901])).
% 14.70/6.88  tff(c_8245, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8159, c_3929])).
% 14.70/6.88  tff(c_8250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8139, c_8245])).
% 14.70/6.88  tff(c_8251, plain, (![B_65]: (r1_tarski('#skF_2', B_65))), inference(splitRight, [status(thm)], [c_4011])).
% 14.70/6.88  tff(c_8394, plain, (![B_561, A_562, C_563]: (k1_xboole_0=B_561 | k1_relset_1(A_562, B_561, C_563)=A_562 | ~v1_funct_2(C_563, A_562, B_561) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(A_562, B_561))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.70/6.88  tff(c_8404, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_8394])).
% 14.70/6.88  tff(c_8415, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3856, c_8404])).
% 14.70/6.88  tff(c_8431, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_8415])).
% 14.70/6.88  tff(c_10900, plain, (![A_681]: (v5_relat_1(k2_funct_1(A_681), k1_relat_1(A_681)) | ~v1_relat_1(k2_funct_1(A_681)) | ~v2_funct_1(A_681) | ~v1_funct_1(A_681) | ~v1_relat_1(A_681))), inference(superposition, [status(thm), theory('equality')], [c_3607, c_286])).
% 14.70/6.88  tff(c_10905, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8431, c_10900])).
% 14.70/6.88  tff(c_10911, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_10905])).
% 14.70/6.88  tff(c_10928, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10911])).
% 14.70/6.88  tff(c_10931, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_10928])).
% 14.70/6.88  tff(c_10935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_10931])).
% 14.70/6.88  tff(c_10937, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10911])).
% 14.70/6.88  tff(c_10936, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_10911])).
% 14.70/6.88  tff(c_10912, plain, (![A_682, A_683]: (r1_tarski(k1_relat_1(A_682), A_683) | ~v5_relat_1(k2_funct_1(A_682), A_683) | ~v1_relat_1(k2_funct_1(A_682)) | ~v2_funct_1(A_682) | ~v1_funct_1(A_682) | ~v1_relat_1(A_682))), inference(superposition, [status(thm), theory('equality')], [c_3607, c_22])).
% 14.70/6.88  tff(c_11822, plain, (![A_696]: (r1_tarski(k1_relat_1(A_696), k2_relat_1(k2_funct_1(A_696))) | ~v2_funct_1(A_696) | ~v1_funct_1(A_696) | ~v1_relat_1(A_696) | ~v1_relat_1(k2_funct_1(A_696)))), inference(resolution, [status(thm)], [c_286, c_10912])).
% 14.70/6.88  tff(c_11833, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8431, c_11822])).
% 14.70/6.88  tff(c_11844, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10937, c_152, c_70, c_64, c_11833])).
% 14.70/6.88  tff(c_11848, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_11844, c_237])).
% 14.70/6.88  tff(c_11859, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10937, c_10936, c_11848])).
% 14.70/6.88  tff(c_11988, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11859, c_3759])).
% 14.70/6.88  tff(c_12068, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10937, c_162, c_11988])).
% 14.70/6.88  tff(c_12217, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_12068])).
% 14.70/6.88  tff(c_12234, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_3895, c_12217])).
% 14.70/6.88  tff(c_12236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_12234])).
% 14.70/6.88  tff(c_12237, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_8415])).
% 14.70/6.88  tff(c_8252, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_4011])).
% 14.70/6.88  tff(c_12240, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12237, c_8252])).
% 14.70/6.88  tff(c_12294, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_12240, c_2])).
% 14.70/6.88  tff(c_12300, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8251, c_12294])).
% 14.70/6.88  tff(c_12261, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12237, c_12237, c_10])).
% 14.70/6.88  tff(c_12445, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12300, c_12300, c_12261])).
% 14.70/6.88  tff(c_109, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.70/6.88  tff(c_113, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_109])).
% 14.70/6.88  tff(c_121, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(B_40, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.70/6.88  tff(c_126, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_113, c_121])).
% 14.70/6.88  tff(c_245, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_126])).
% 14.70/6.88  tff(c_12314, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12300, c_245])).
% 14.70/6.88  tff(c_12547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_12445, c_12314])).
% 14.70/6.88  tff(c_12548, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_126])).
% 14.70/6.88  tff(c_12551, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12548, c_66])).
% 14.70/6.88  tff(c_16411, plain, (![A_959, B_960, C_961]: (k1_relset_1(A_959, B_960, C_961)=k1_relat_1(C_961) | ~m1_subset_1(C_961, k1_zfmisc_1(k2_zfmisc_1(A_959, B_960))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.70/6.88  tff(c_16455, plain, (![C_967]: (k1_relset_1('#skF_1', '#skF_2', C_967)=k1_relat_1(C_967) | ~m1_subset_1(C_967, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12548, c_16411])).
% 14.70/6.88  tff(c_16463, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12551, c_16455])).
% 14.70/6.88  tff(c_16514, plain, (![A_974, B_975, C_976]: (k2_relset_1(A_974, B_975, C_976)=k2_relat_1(C_976) | ~m1_subset_1(C_976, k1_zfmisc_1(k2_zfmisc_1(A_974, B_975))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.70/6.88  tff(c_16558, plain, (![C_982]: (k2_relset_1('#skF_1', '#skF_2', C_982)=k2_relat_1(C_982) | ~m1_subset_1(C_982, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12548, c_16514])).
% 14.70/6.88  tff(c_16561, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12551, c_16558])).
% 14.70/6.88  tff(c_16567, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16561])).
% 14.70/6.88  tff(c_20147, plain, (![B_1183, C_1184, A_1185]: (k1_xboole_0=B_1183 | v1_funct_2(C_1184, A_1185, B_1183) | k1_relset_1(A_1185, B_1183, C_1184)!=A_1185 | ~m1_subset_1(C_1184, k1_zfmisc_1(k2_zfmisc_1(A_1185, B_1183))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.70/6.88  tff(c_20156, plain, (![C_1184]: (k1_xboole_0='#skF_2' | v1_funct_2(C_1184, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_1184)!='#skF_1' | ~m1_subset_1(C_1184, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12548, c_20147])).
% 14.70/6.88  tff(c_20260, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_20156])).
% 14.70/6.88  tff(c_17104, plain, (![B_1028, A_1029, C_1030]: (k1_xboole_0=B_1028 | k1_relset_1(A_1029, B_1028, C_1030)=A_1029 | ~v1_funct_2(C_1030, A_1029, B_1028) | ~m1_subset_1(C_1030, k1_zfmisc_1(k2_zfmisc_1(A_1029, B_1028))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.70/6.88  tff(c_17113, plain, (![C_1030]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_1030)='#skF_1' | ~v1_funct_2(C_1030, '#skF_1', '#skF_2') | ~m1_subset_1(C_1030, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12548, c_17104])).
% 14.70/6.88  tff(c_17622, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_17113])).
% 14.70/6.88  tff(c_16601, plain, (![A_10]: (v5_relat_1('#skF_3', A_10) | ~r1_tarski('#skF_2', A_10) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16567, c_20])).
% 14.70/6.88  tff(c_16668, plain, (![A_986]: (v5_relat_1('#skF_3', A_986) | ~r1_tarski('#skF_2', A_986))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_16601])).
% 14.70/6.88  tff(c_12650, plain, (![A_723, B_724, A_725]: (v5_relat_1(A_723, B_724) | ~r1_tarski(A_723, k2_zfmisc_1(A_725, B_724)))), inference(resolution, [status(thm)], [c_16, c_174])).
% 14.70/6.88  tff(c_16270, plain, (![B_942, B_943, A_944]: (v5_relat_1(k2_relat_1(B_942), B_943) | ~v5_relat_1(B_942, k2_zfmisc_1(A_944, B_943)) | ~v1_relat_1(B_942))), inference(resolution, [status(thm)], [c_22, c_12650])).
% 14.70/6.88  tff(c_16285, plain, (![B_942, B_4]: (v5_relat_1(k2_relat_1(B_942), B_4) | ~v5_relat_1(B_942, k1_xboole_0) | ~v1_relat_1(B_942))), inference(superposition, [status(thm), theory('equality')], [c_12, c_16270])).
% 14.70/6.88  tff(c_16580, plain, (![B_4]: (v5_relat_1('#skF_2', B_4) | ~v5_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16567, c_16285])).
% 14.70/6.88  tff(c_16612, plain, (![B_4]: (v5_relat_1('#skF_2', B_4) | ~v5_relat_1('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_16580])).
% 14.70/6.88  tff(c_16631, plain, (~v5_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_16612])).
% 14.70/6.88  tff(c_16681, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_16668, c_16631])).
% 14.70/6.88  tff(c_17637, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17622, c_16681])).
% 14.70/6.88  tff(c_17673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_17637])).
% 14.70/6.88  tff(c_17933, plain, (![C_1082]: (k1_relset_1('#skF_1', '#skF_2', C_1082)='#skF_1' | ~v1_funct_2(C_1082, '#skF_1', '#skF_2') | ~m1_subset_1(C_1082, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_17113])).
% 14.70/6.88  tff(c_17936, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12551, c_17933])).
% 14.70/6.88  tff(c_17943, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16463, c_17936])).
% 14.70/6.88  tff(c_12684, plain, (![A_730]: (k2_relat_1(k2_funct_1(A_730))=k1_relat_1(A_730) | ~v2_funct_1(A_730) | ~v1_funct_1(A_730) | ~v1_relat_1(A_730))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.70/6.88  tff(c_12593, plain, (![B_711, A_712]: (v5_relat_1(B_711, A_712) | ~r1_tarski(k2_relat_1(B_711), A_712) | ~v1_relat_1(B_711))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.70/6.88  tff(c_12602, plain, (![B_711]: (v5_relat_1(B_711, k2_relat_1(B_711)) | ~v1_relat_1(B_711))), inference(resolution, [status(thm)], [c_6, c_12593])).
% 14.70/6.88  tff(c_18310, plain, (![A_1109]: (v5_relat_1(k2_funct_1(A_1109), k1_relat_1(A_1109)) | ~v1_relat_1(k2_funct_1(A_1109)) | ~v2_funct_1(A_1109) | ~v1_funct_1(A_1109) | ~v1_relat_1(A_1109))), inference(superposition, [status(thm), theory('equality')], [c_12684, c_12602])).
% 14.70/6.88  tff(c_18318, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17943, c_18310])).
% 14.70/6.88  tff(c_18326, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_18318])).
% 14.70/6.88  tff(c_18327, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_18326])).
% 14.70/6.88  tff(c_18357, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_18327])).
% 14.70/6.88  tff(c_18361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_18357])).
% 14.70/6.88  tff(c_18363, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_18326])).
% 14.70/6.88  tff(c_30, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.70/6.88  tff(c_16134, plain, (![A_930]: (m1_subset_1(A_930, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_930), k2_relat_1(A_930)))) | ~v1_funct_1(A_930) | ~v1_relat_1(A_930))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.70/6.88  tff(c_19504, plain, (![A_1141]: (m1_subset_1(k2_funct_1(A_1141), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1141)), k1_relat_1(A_1141)))) | ~v1_funct_1(k2_funct_1(A_1141)) | ~v1_relat_1(k2_funct_1(A_1141)) | ~v2_funct_1(A_1141) | ~v1_funct_1(A_1141) | ~v1_relat_1(A_1141))), inference(superposition, [status(thm), theory('equality')], [c_30, c_16134])).
% 14.70/6.88  tff(c_19531, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17943, c_19504])).
% 14.70/6.88  tff(c_19549, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_18363, c_162, c_19531])).
% 14.70/6.88  tff(c_19586, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_19549])).
% 14.70/6.88  tff(c_19603, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_16567, c_19586])).
% 14.70/6.88  tff(c_19605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_213, c_19603])).
% 14.70/6.88  tff(c_19607, plain, (v5_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_16612])).
% 14.70/6.88  tff(c_16604, plain, (![A_10]: (r1_tarski('#skF_2', A_10) | ~v5_relat_1('#skF_3', A_10) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16567, c_22])).
% 14.70/6.88  tff(c_19675, plain, (![A_1146]: (r1_tarski('#skF_2', A_1146) | ~v5_relat_1('#skF_3', A_1146))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_16604])).
% 14.70/6.88  tff(c_19694, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_19607, c_19675])).
% 14.97/6.88  tff(c_19721, plain, (k1_xboole_0='#skF_2' | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_19694, c_2])).
% 14.97/6.88  tff(c_19722, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_19721])).
% 14.97/6.88  tff(c_20278, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20260, c_19722])).
% 14.97/6.88  tff(c_20318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_20278])).
% 14.97/6.88  tff(c_20320, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_20156])).
% 14.97/6.88  tff(c_20211, plain, (![B_1194, A_1195, C_1196]: (k1_xboole_0=B_1194 | k1_relset_1(A_1195, B_1194, C_1196)=A_1195 | ~v1_funct_2(C_1196, A_1195, B_1194) | ~m1_subset_1(C_1196, k1_zfmisc_1(k2_zfmisc_1(A_1195, B_1194))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_20220, plain, (![C_1196]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_1196)='#skF_1' | ~v1_funct_2(C_1196, '#skF_1', '#skF_2') | ~m1_subset_1(C_1196, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12548, c_20211])).
% 14.97/6.88  tff(c_20412, plain, (![C_1207]: (k1_relset_1('#skF_1', '#skF_2', C_1207)='#skF_1' | ~v1_funct_2(C_1207, '#skF_1', '#skF_2') | ~m1_subset_1(C_1207, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_20320, c_20220])).
% 14.97/6.88  tff(c_20415, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12551, c_20412])).
% 14.97/6.88  tff(c_20422, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16463, c_20415])).
% 14.97/6.88  tff(c_21080, plain, (![A_1258]: (v5_relat_1(k2_funct_1(A_1258), k1_relat_1(A_1258)) | ~v1_relat_1(k2_funct_1(A_1258)) | ~v2_funct_1(A_1258) | ~v1_funct_1(A_1258) | ~v1_relat_1(A_1258))), inference(superposition, [status(thm), theory('equality')], [c_12684, c_12602])).
% 14.97/6.88  tff(c_21088, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20422, c_21080])).
% 14.97/6.88  tff(c_21096, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_21088])).
% 14.97/6.88  tff(c_21097, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_21096])).
% 14.97/6.88  tff(c_21100, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_21097])).
% 14.97/6.88  tff(c_21104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_21100])).
% 14.97/6.88  tff(c_21106, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_21096])).
% 14.97/6.88  tff(c_21105, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_21096])).
% 14.97/6.88  tff(c_21011, plain, (![A_1253, A_1254]: (r1_tarski(k1_relat_1(A_1253), A_1254) | ~v5_relat_1(k2_funct_1(A_1253), A_1254) | ~v1_relat_1(k2_funct_1(A_1253)) | ~v2_funct_1(A_1253) | ~v1_funct_1(A_1253) | ~v1_relat_1(A_1253))), inference(superposition, [status(thm), theory('equality')], [c_12684, c_22])).
% 14.97/6.88  tff(c_21264, plain, (![A_1268]: (r1_tarski(k1_relat_1(A_1268), k2_relat_1(k2_funct_1(A_1268))) | ~v2_funct_1(A_1268) | ~v1_funct_1(A_1268) | ~v1_relat_1(A_1268) | ~v1_relat_1(k2_funct_1(A_1268)))), inference(resolution, [status(thm)], [c_12602, c_21011])).
% 14.97/6.88  tff(c_21275, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20422, c_21264])).
% 14.97/6.88  tff(c_21286, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_21106, c_152, c_70, c_64, c_21275])).
% 14.97/6.88  tff(c_21290, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_21286, c_237])).
% 14.97/6.88  tff(c_21301, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21106, c_21105, c_21290])).
% 14.97/6.88  tff(c_16158, plain, (![A_930]: (r1_tarski(A_930, k2_zfmisc_1(k1_relat_1(A_930), k2_relat_1(A_930))) | ~v1_funct_1(A_930) | ~v1_relat_1(A_930))), inference(resolution, [status(thm)], [c_16134, c_14])).
% 14.97/6.88  tff(c_21400, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_21301, c_16158])).
% 14.97/6.88  tff(c_21481, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_21106, c_162, c_21400])).
% 14.97/6.88  tff(c_21654, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_21481])).
% 14.97/6.88  tff(c_21671, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_16567, c_21654])).
% 14.97/6.88  tff(c_21673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_21671])).
% 14.97/6.88  tff(c_21674, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_19721])).
% 14.97/6.88  tff(c_16292, plain, (![A_5, B_943]: (v5_relat_1(k2_relat_1(A_5), B_943) | ~v1_relat_1(A_5) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_243, c_16270])).
% 14.97/6.88  tff(c_16577, plain, (![B_943]: (v5_relat_1('#skF_2', B_943) | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_3', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16567, c_16292])).
% 14.97/6.88  tff(c_16610, plain, (![B_943]: (v5_relat_1('#skF_2', B_943) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_16577])).
% 14.97/6.88  tff(c_16630, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_16610])).
% 14.97/6.88  tff(c_21688, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21674, c_16630])).
% 14.97/6.88  tff(c_21716, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21674, c_21674, c_10])).
% 14.97/6.88  tff(c_16583, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16567, c_16158])).
% 14.97/6.88  tff(c_16614, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_16583])).
% 14.97/6.88  tff(c_21802, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21716, c_16614])).
% 14.97/6.88  tff(c_21804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21688, c_21802])).
% 14.97/6.88  tff(c_21806, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_16610])).
% 14.97/6.88  tff(c_21919, plain, (![A_1286]: (r1_tarski('#skF_2', A_1286) | ~v5_relat_1('#skF_3', A_1286))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_16604])).
% 14.97/6.88  tff(c_21934, plain, (![B_65]: (r1_tarski('#skF_2', B_65) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_243, c_21919])).
% 14.97/6.88  tff(c_21947, plain, (![B_65]: (r1_tarski('#skF_2', B_65))), inference(demodulation, [status(thm), theory('equality')], [c_21806, c_21934])).
% 14.97/6.88  tff(c_22121, plain, (![B_1298, A_1299, C_1300]: (k1_xboole_0=B_1298 | k1_relset_1(A_1299, B_1298, C_1300)=A_1299 | ~v1_funct_2(C_1300, A_1299, B_1298) | ~m1_subset_1(C_1300, k1_zfmisc_1(k2_zfmisc_1(A_1299, B_1298))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_22130, plain, (![C_1300]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_1300)='#skF_1' | ~v1_funct_2(C_1300, '#skF_1', '#skF_2') | ~m1_subset_1(C_1300, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_12548, c_22121])).
% 14.97/6.88  tff(c_22253, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_22130])).
% 14.97/6.88  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.97/6.88  tff(c_12562, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_12548, c_8])).
% 14.97/6.88  tff(c_12581, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_12562])).
% 14.97/6.88  tff(c_21836, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_21806, c_2])).
% 14.97/6.88  tff(c_21846, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_12581, c_21836])).
% 14.97/6.88  tff(c_22264, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22253, c_21846])).
% 14.97/6.88  tff(c_22299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21947, c_22264])).
% 14.97/6.88  tff(c_23521, plain, (![C_1363]: (k1_relset_1('#skF_1', '#skF_2', C_1363)='#skF_1' | ~v1_funct_2(C_1363, '#skF_1', '#skF_2') | ~m1_subset_1(C_1363, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_22130])).
% 14.97/6.88  tff(c_23524, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_12551, c_23521])).
% 14.97/6.88  tff(c_23531, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16463, c_23524])).
% 14.97/6.88  tff(c_25958, plain, (![A_1426]: (v5_relat_1(k2_funct_1(A_1426), k1_relat_1(A_1426)) | ~v1_relat_1(k2_funct_1(A_1426)) | ~v2_funct_1(A_1426) | ~v1_funct_1(A_1426) | ~v1_relat_1(A_1426))), inference(superposition, [status(thm), theory('equality')], [c_12684, c_12602])).
% 14.97/6.88  tff(c_25966, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23531, c_25958])).
% 14.97/6.88  tff(c_25974, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_25966])).
% 14.97/6.88  tff(c_25975, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_25974])).
% 14.97/6.88  tff(c_25978, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_25975])).
% 14.97/6.88  tff(c_25982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_25978])).
% 14.97/6.88  tff(c_25984, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_25974])).
% 14.97/6.88  tff(c_25983, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_25974])).
% 14.97/6.88  tff(c_24827, plain, (![A_1404, A_1405]: (r1_tarski(k1_relat_1(A_1404), A_1405) | ~v5_relat_1(k2_funct_1(A_1404), A_1405) | ~v1_relat_1(k2_funct_1(A_1404)) | ~v2_funct_1(A_1404) | ~v1_funct_1(A_1404) | ~v1_relat_1(A_1404))), inference(superposition, [status(thm), theory('equality')], [c_12684, c_22])).
% 14.97/6.88  tff(c_26399, plain, (![A_1434]: (r1_tarski(k1_relat_1(A_1434), k2_relat_1(k2_funct_1(A_1434))) | ~v2_funct_1(A_1434) | ~v1_funct_1(A_1434) | ~v1_relat_1(A_1434) | ~v1_relat_1(k2_funct_1(A_1434)))), inference(resolution, [status(thm)], [c_12602, c_24827])).
% 14.97/6.88  tff(c_26410, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_23531, c_26399])).
% 14.97/6.88  tff(c_26421, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_25984, c_152, c_70, c_64, c_26410])).
% 14.97/6.88  tff(c_26425, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_26421, c_237])).
% 14.97/6.88  tff(c_26436, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25984, c_25983, c_26425])).
% 14.97/6.88  tff(c_26729, plain, (![A_1437]: (m1_subset_1(k2_funct_1(A_1437), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1437), k2_relat_1(k2_funct_1(A_1437))))) | ~v1_funct_1(k2_funct_1(A_1437)) | ~v1_relat_1(k2_funct_1(A_1437)) | ~v2_funct_1(A_1437) | ~v1_funct_1(A_1437) | ~v1_relat_1(A_1437))), inference(superposition, [status(thm), theory('equality')], [c_32, c_16134])).
% 14.97/6.88  tff(c_26759, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26436, c_26729])).
% 14.97/6.88  tff(c_26812, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_25984, c_162, c_16567, c_26759])).
% 14.97/6.88  tff(c_26814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_213, c_26812])).
% 14.97/6.88  tff(c_26816, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_12562])).
% 14.97/6.88  tff(c_26824, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26816, c_26816, c_12])).
% 14.97/6.88  tff(c_26815, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_12562])).
% 14.97/6.88  tff(c_26830, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26816, c_26816, c_26815])).
% 14.97/6.88  tff(c_26831, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_26830])).
% 14.97/6.88  tff(c_26834, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26831, c_213])).
% 14.97/6.88  tff(c_26900, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26824, c_26834])).
% 14.97/6.88  tff(c_26822, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26816, c_26816, c_10])).
% 14.97/6.88  tff(c_27269, plain, (![A_1496, B_1497, C_1498]: (k2_relset_1(A_1496, B_1497, C_1498)=k2_relat_1(C_1498) | ~m1_subset_1(C_1498, k1_zfmisc_1(k2_zfmisc_1(A_1496, B_1497))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.97/6.88  tff(c_27360, plain, (![A_1512, C_1513]: (k2_relset_1(A_1512, '#skF_3', C_1513)=k2_relat_1(C_1513) | ~m1_subset_1(C_1513, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_26822, c_27269])).
% 14.97/6.88  tff(c_27377, plain, (![A_1516]: (k2_relset_1(A_1516, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_12551, c_27360])).
% 14.97/6.88  tff(c_26836, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26831, c_26831, c_62])).
% 14.97/6.88  tff(c_27384, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_27377, c_26836])).
% 14.97/6.88  tff(c_27004, plain, (![A_1466]: (k1_relat_1(k2_funct_1(A_1466))=k2_relat_1(A_1466) | ~v2_funct_1(A_1466) | ~v1_funct_1(A_1466) | ~v1_relat_1(A_1466))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.97/6.88  tff(c_56, plain, (![A_28]: (v1_funct_2(A_28, k1_relat_1(A_28), k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.97/6.88  tff(c_30113, plain, (![A_1629]: (v1_funct_2(k2_funct_1(A_1629), k2_relat_1(A_1629), k2_relat_1(k2_funct_1(A_1629))) | ~v1_funct_1(k2_funct_1(A_1629)) | ~v1_relat_1(k2_funct_1(A_1629)) | ~v2_funct_1(A_1629) | ~v1_funct_1(A_1629) | ~v1_relat_1(A_1629))), inference(superposition, [status(thm), theory('equality')], [c_27004, c_56])).
% 14.97/6.88  tff(c_30134, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_27384, c_30113])).
% 14.97/6.88  tff(c_30144, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_162, c_30134])).
% 14.97/6.88  tff(c_30245, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_30144])).
% 14.97/6.88  tff(c_30248, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_30245])).
% 14.97/6.88  tff(c_30252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_30248])).
% 14.97/6.88  tff(c_30254, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_30144])).
% 14.97/6.88  tff(c_27088, plain, (![A_1475]: (m1_subset_1(A_1475, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1475), k2_relat_1(A_1475)))) | ~v1_funct_1(A_1475) | ~v1_relat_1(A_1475))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.97/6.88  tff(c_30320, plain, (![A_1634]: (m1_subset_1(k2_funct_1(A_1634), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1634), k2_relat_1(k2_funct_1(A_1634))))) | ~v1_funct_1(k2_funct_1(A_1634)) | ~v1_relat_1(k2_funct_1(A_1634)) | ~v2_funct_1(A_1634) | ~v1_funct_1(A_1634) | ~v1_relat_1(A_1634))), inference(superposition, [status(thm), theory('equality')], [c_32, c_27088])).
% 14.97/6.88  tff(c_30365, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_27384, c_30320])).
% 14.97/6.88  tff(c_30390, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_30254, c_162, c_26824, c_30365])).
% 14.97/6.88  tff(c_30392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26900, c_30390])).
% 14.97/6.88  tff(c_30393, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_26830])).
% 14.97/6.88  tff(c_30458, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_30393, c_26822])).
% 14.97/6.88  tff(c_30399, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_213])).
% 14.97/6.88  tff(c_30518, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30458, c_30399])).
% 14.97/6.88  tff(c_30403, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_152])).
% 14.97/6.88  tff(c_30407, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_70])).
% 14.97/6.88  tff(c_30406, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_64])).
% 14.97/6.88  tff(c_30394, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_26830])).
% 14.97/6.88  tff(c_30412, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_30394])).
% 14.97/6.88  tff(c_30440, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_30393, c_26824])).
% 14.97/6.88  tff(c_30396, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_30393, c_12551])).
% 14.97/6.88  tff(c_30896, plain, (![A_1698, B_1699, C_1700]: (k1_relset_1(A_1698, B_1699, C_1700)=k1_relat_1(C_1700) | ~m1_subset_1(C_1700, k1_zfmisc_1(k2_zfmisc_1(A_1698, B_1699))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.97/6.88  tff(c_31392, plain, (![B_1733, C_1734]: (k1_relset_1('#skF_1', B_1733, C_1734)=k1_relat_1(C_1734) | ~m1_subset_1(C_1734, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_30440, c_30896])).
% 14.97/6.88  tff(c_31401, plain, (![B_1735]: (k1_relset_1('#skF_1', B_1735, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_30396, c_31392])).
% 14.97/6.88  tff(c_30405, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_68])).
% 14.97/6.88  tff(c_30395, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_26816])).
% 14.97/6.88  tff(c_50, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_xboole_0 | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_71, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_xboole_0 | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_50])).
% 14.97/6.88  tff(c_31293, plain, (![B_1721, C_1722]: (k1_relset_1('#skF_1', B_1721, C_1722)='#skF_1' | ~v1_funct_2(C_1722, '#skF_1', B_1721) | ~m1_subset_1(C_1722, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30395, c_30395, c_30395, c_30395, c_71])).
% 14.97/6.88  tff(c_31300, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_30405, c_31293])).
% 14.97/6.88  tff(c_31310, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30396, c_31300])).
% 14.97/6.88  tff(c_31408, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_31401, c_31310])).
% 14.97/6.88  tff(c_30736, plain, (![A_1679, B_1680, C_1681]: (k2_relset_1(A_1679, B_1680, C_1681)=k2_relat_1(C_1681) | ~m1_subset_1(C_1681, k1_zfmisc_1(k2_zfmisc_1(A_1679, B_1680))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.97/6.88  tff(c_30818, plain, (![B_1694, C_1695]: (k2_relset_1('#skF_1', B_1694, C_1695)=k2_relat_1(C_1695) | ~m1_subset_1(C_1695, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_30440, c_30736])).
% 14.97/6.88  tff(c_30826, plain, (![B_1696]: (k2_relset_1('#skF_1', B_1696, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_30396, c_30818])).
% 14.97/6.88  tff(c_30404, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_62])).
% 14.97/6.88  tff(c_30833, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_30826, c_30404])).
% 14.97/6.88  tff(c_54, plain, (![A_28]: (m1_subset_1(A_28, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_28), k2_relat_1(A_28)))) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.97/6.88  tff(c_30852, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2'))) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30833, c_54])).
% 14.97/6.88  tff(c_30877, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30403, c_30407, c_30852])).
% 14.97/6.88  tff(c_31041, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_30877, c_14])).
% 14.97/6.88  tff(c_31067, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2')='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_31041, c_2])).
% 14.97/6.88  tff(c_31330, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_31067])).
% 14.97/6.88  tff(c_31422, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31408, c_31330])).
% 14.97/6.88  tff(c_31430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_30440, c_31422])).
% 14.97/6.88  tff(c_31431, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_31067])).
% 14.97/6.88  tff(c_26821, plain, (![B_4, A_3]: (B_4='#skF_3' | A_3='#skF_3' | k2_zfmisc_1(A_3, B_4)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26816, c_26816, c_26816, c_8])).
% 14.97/6.88  tff(c_30612, plain, (![B_4, A_3]: (B_4='#skF_1' | A_3='#skF_1' | k2_zfmisc_1(A_3, B_4)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_30393, c_30393, c_26821])).
% 14.97/6.88  tff(c_31459, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_31431, c_30612])).
% 14.97/6.88  tff(c_31489, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_30412, c_31459])).
% 14.97/6.88  tff(c_30672, plain, (![A_1671]: (k2_relat_1(k2_funct_1(A_1671))=k1_relat_1(A_1671) | ~v2_funct_1(A_1671) | ~v1_funct_1(A_1671) | ~v1_relat_1(A_1671))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.97/6.88  tff(c_32616, plain, (![A_1805, A_1806]: (v5_relat_1(k2_funct_1(A_1805), A_1806) | ~r1_tarski(k1_relat_1(A_1805), A_1806) | ~v1_relat_1(k2_funct_1(A_1805)) | ~v2_funct_1(A_1805) | ~v1_funct_1(A_1805) | ~v1_relat_1(A_1805))), inference(superposition, [status(thm), theory('equality')], [c_30672, c_20])).
% 14.97/6.88  tff(c_187, plain, (![C_48, B_4]: (v5_relat_1(C_48, B_4) | ~m1_subset_1(C_48, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_174])).
% 14.97/6.88  tff(c_26818, plain, (![C_48, B_4]: (v5_relat_1(C_48, B_4) | ~m1_subset_1(C_48, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26816, c_187])).
% 14.97/6.88  tff(c_30508, plain, (![C_1645, B_1646]: (v5_relat_1(C_1645, B_1646) | ~m1_subset_1(C_1645, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_26818])).
% 14.97/6.88  tff(c_30514, plain, (![B_1646]: (v5_relat_1('#skF_1', B_1646))), inference(resolution, [status(thm)], [c_30396, c_30508])).
% 14.97/6.88  tff(c_30873, plain, (![A_10]: (r1_tarski('#skF_2', A_10) | ~v5_relat_1('#skF_1', A_10) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30833, c_22])).
% 14.97/6.88  tff(c_30913, plain, (![A_1701]: (r1_tarski('#skF_2', A_1701))), inference(demodulation, [status(thm), theory('equality')], [c_30403, c_30514, c_30873])).
% 14.97/6.88  tff(c_30975, plain, (![A_1706]: (A_1706='#skF_2' | ~r1_tarski(A_1706, '#skF_2'))), inference(resolution, [status(thm)], [c_30913, c_2])).
% 14.97/6.88  tff(c_30990, plain, (![B_11]: (k2_relat_1(B_11)='#skF_2' | ~v5_relat_1(B_11, '#skF_2') | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_22, c_30975])).
% 14.97/6.88  tff(c_32753, plain, (![A_1813]: (k2_relat_1(k2_funct_1(A_1813))='#skF_2' | ~r1_tarski(k1_relat_1(A_1813), '#skF_2') | ~v1_relat_1(k2_funct_1(A_1813)) | ~v2_funct_1(A_1813) | ~v1_funct_1(A_1813) | ~v1_relat_1(A_1813))), inference(resolution, [status(thm)], [c_32616, c_30990])).
% 14.97/6.88  tff(c_32756, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_2' | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31489, c_32753])).
% 14.97/6.88  tff(c_32761, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_2' | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30403, c_30407, c_30406, c_32756])).
% 14.97/6.88  tff(c_32762, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_32761])).
% 14.97/6.88  tff(c_32765, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_28, c_32762])).
% 14.97/6.88  tff(c_32769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30403, c_30407, c_32765])).
% 14.97/6.88  tff(c_32771, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_32761])).
% 14.97/6.88  tff(c_30402, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30393, c_162])).
% 14.97/6.88  tff(c_30775, plain, (![A_1690]: (m1_subset_1(A_1690, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1690), k2_relat_1(A_1690)))) | ~v1_funct_1(A_1690) | ~v1_relat_1(A_1690))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.97/6.88  tff(c_33797, plain, (![A_1827]: (m1_subset_1(k2_funct_1(A_1827), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1827)), k1_relat_1(A_1827)))) | ~v1_funct_1(k2_funct_1(A_1827)) | ~v1_relat_1(k2_funct_1(A_1827)) | ~v2_funct_1(A_1827) | ~v1_funct_1(A_1827) | ~v1_relat_1(A_1827))), inference(superposition, [status(thm), theory('equality')], [c_30, c_30775])).
% 14.97/6.88  tff(c_33824, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_31489, c_33797])).
% 14.97/6.88  tff(c_33842, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30403, c_30407, c_30406, c_32771, c_30402, c_30458, c_33824])).
% 14.97/6.88  tff(c_33844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30518, c_33842])).
% 14.97/6.88  tff(c_33845, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_161])).
% 14.97/6.88  tff(c_36129, plain, (![A_2031, B_2032, C_2033]: (k2_relset_1(A_2031, B_2032, C_2033)=k2_relat_1(C_2033) | ~m1_subset_1(C_2033, k1_zfmisc_1(k2_zfmisc_1(A_2031, B_2032))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.97/6.88  tff(c_36142, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_36129])).
% 14.97/6.88  tff(c_36153, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_36142])).
% 14.97/6.88  tff(c_33846, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_161])).
% 14.97/6.88  tff(c_36022, plain, (![A_2018, B_2019, C_2020]: (k1_relset_1(A_2018, B_2019, C_2020)=k1_relat_1(C_2020) | ~m1_subset_1(C_2020, k1_zfmisc_1(k2_zfmisc_1(A_2018, B_2019))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.97/6.88  tff(c_36039, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_33846, c_36022])).
% 14.97/6.88  tff(c_36387, plain, (![B_2052, C_2053, A_2054]: (k1_xboole_0=B_2052 | v1_funct_2(C_2053, A_2054, B_2052) | k1_relset_1(A_2054, B_2052, C_2053)!=A_2054 | ~m1_subset_1(C_2053, k1_zfmisc_1(k2_zfmisc_1(A_2054, B_2052))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_36396, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_33846, c_36387])).
% 14.97/6.88  tff(c_36415, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36039, c_36396])).
% 14.97/6.88  tff(c_36416, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_33845, c_36415])).
% 14.97/6.88  tff(c_36421, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_36416])).
% 14.97/6.88  tff(c_36424, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_36421])).
% 14.97/6.88  tff(c_36427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_36153, c_36424])).
% 14.97/6.88  tff(c_36428, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_36416])).
% 14.97/6.88  tff(c_33896, plain, (![C_1837, B_1838]: (v5_relat_1(C_1837, B_1838) | ~m1_subset_1(C_1837, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_174])).
% 14.97/6.88  tff(c_33900, plain, (![A_5, B_1838]: (v5_relat_1(A_5, B_1838) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_33896])).
% 14.97/6.88  tff(c_36174, plain, (![A_10]: (r1_tarski('#skF_2', A_10) | ~v5_relat_1('#skF_3', A_10) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36153, c_22])).
% 14.97/6.88  tff(c_36200, plain, (![A_2034]: (r1_tarski('#skF_2', A_2034) | ~v5_relat_1('#skF_3', A_2034))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_36174])).
% 14.97/6.88  tff(c_36212, plain, (![B_1838]: (r1_tarski('#skF_2', B_1838) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_33900, c_36200])).
% 14.97/6.88  tff(c_36234, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_36212])).
% 14.97/6.88  tff(c_36442, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36428, c_36234])).
% 14.97/6.88  tff(c_36464, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36428, c_36428, c_12])).
% 14.97/6.88  tff(c_36581, plain, (r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36464, c_113])).
% 14.97/6.88  tff(c_36584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36442, c_36581])).
% 14.97/6.88  tff(c_36585, plain, (![B_1838]: (r1_tarski('#skF_2', B_1838))), inference(splitRight, [status(thm)], [c_36212])).
% 14.97/6.88  tff(c_36041, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_36022])).
% 14.97/6.88  tff(c_37034, plain, (![B_2076, A_2077, C_2078]: (k1_xboole_0=B_2076 | k1_relset_1(A_2077, B_2076, C_2078)=A_2077 | ~v1_funct_2(C_2078, A_2077, B_2076) | ~m1_subset_1(C_2078, k1_zfmisc_1(k2_zfmisc_1(A_2077, B_2076))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_37050, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_37034])).
% 14.97/6.88  tff(c_37066, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_36041, c_37050])).
% 14.97/6.88  tff(c_37068, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_37066])).
% 14.97/6.88  tff(c_18, plain, (![B_9, A_7]: (v1_relat_1(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.97/6.88  tff(c_33855, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_33846, c_18])).
% 14.97/6.88  tff(c_33863, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_33855])).
% 14.97/6.88  tff(c_37174, plain, (![B_2084, C_2085, A_2086]: (k1_xboole_0=B_2084 | v1_funct_2(C_2085, A_2086, B_2084) | k1_relset_1(A_2086, B_2084, C_2085)!=A_2086 | ~m1_subset_1(C_2085, k1_zfmisc_1(k2_zfmisc_1(A_2086, B_2084))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_37180, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_33846, c_37174])).
% 14.97/6.88  tff(c_37196, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36039, c_37180])).
% 14.97/6.88  tff(c_37197, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_33845, c_37196])).
% 14.97/6.88  tff(c_37203, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_37197])).
% 14.97/6.88  tff(c_37206, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_37203])).
% 14.97/6.88  tff(c_37209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_36153, c_37206])).
% 14.97/6.88  tff(c_37210, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_37197])).
% 14.97/6.88  tff(c_37239, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37210, c_37210, c_10])).
% 14.97/6.88  tff(c_37421, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_37239, c_33846])).
% 14.97/6.88  tff(c_37566, plain, (![C_2104, B_2105]: (v5_relat_1(C_2104, B_2105) | ~m1_subset_1(C_2104, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_37210, c_187])).
% 14.97/6.88  tff(c_37583, plain, (![B_2106]: (v5_relat_1(k2_funct_1('#skF_3'), B_2106))), inference(resolution, [status(thm)], [c_37421, c_37566])).
% 14.97/6.88  tff(c_36590, plain, (![B_2060]: (r1_tarski('#skF_2', B_2060))), inference(splitRight, [status(thm)], [c_36212])).
% 14.97/6.88  tff(c_36665, plain, (![B_2067]: (B_2067='#skF_2' | ~r1_tarski(B_2067, '#skF_2'))), inference(resolution, [status(thm)], [c_36590, c_2])).
% 14.97/6.88  tff(c_36680, plain, (![B_11]: (k2_relat_1(B_11)='#skF_2' | ~v5_relat_1(B_11, '#skF_2') | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_22, c_36665])).
% 14.97/6.88  tff(c_37587, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_37583, c_36680])).
% 14.97/6.88  tff(c_37595, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_33863, c_37587])).
% 14.97/6.88  tff(c_37622, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37595, c_30])).
% 14.97/6.88  tff(c_37643, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_37068, c_37622])).
% 14.97/6.88  tff(c_37669, plain, (![B_1838]: (r1_tarski('#skF_1', B_1838))), inference(demodulation, [status(thm), theory('equality')], [c_37643, c_36585])).
% 14.97/6.88  tff(c_33864, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_33846, c_14])).
% 14.97/6.88  tff(c_33874, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_33864, c_2])).
% 14.97/6.88  tff(c_33894, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_33874])).
% 14.97/6.88  tff(c_37419, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_37239, c_33894])).
% 14.97/6.88  tff(c_37720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37669, c_37419])).
% 14.97/6.88  tff(c_37721, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_37066])).
% 14.97/6.88  tff(c_36586, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_36212])).
% 14.97/6.88  tff(c_36617, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_36586, c_2])).
% 14.97/6.88  tff(c_36657, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_36617])).
% 14.97/6.88  tff(c_37728, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37721, c_36657])).
% 14.97/6.88  tff(c_37751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36585, c_37728])).
% 14.97/6.88  tff(c_37752, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_36617])).
% 14.97/6.88  tff(c_48, plain, (![B_26, C_27, A_25]: (k1_xboole_0=B_26 | v1_funct_2(C_27, A_25, B_26) | k1_relset_1(A_25, B_26, C_27)!=A_25 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_38186, plain, (![B_2137, C_2138, A_2139]: (B_2137='#skF_3' | v1_funct_2(C_2138, A_2139, B_2137) | k1_relset_1(A_2139, B_2137, C_2138)!=A_2139 | ~m1_subset_1(C_2138, k1_zfmisc_1(k2_zfmisc_1(A_2139, B_2137))))), inference(demodulation, [status(thm), theory('equality')], [c_37752, c_48])).
% 14.97/6.88  tff(c_38198, plain, ('#skF_3'='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_33846, c_38186])).
% 14.97/6.88  tff(c_38209, plain, ('#skF_3'='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36039, c_38198])).
% 14.97/6.88  tff(c_38210, plain, ('#skF_3'='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_33845, c_38209])).
% 14.97/6.88  tff(c_38300, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_38210])).
% 14.97/6.88  tff(c_38303, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_38300])).
% 14.97/6.88  tff(c_38306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_36153, c_38303])).
% 14.97/6.88  tff(c_38307, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_38210])).
% 14.97/6.88  tff(c_37775, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37752, c_37752, c_12])).
% 14.97/6.88  tff(c_38325, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38307, c_38307, c_37775])).
% 14.97/6.88  tff(c_33865, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_126])).
% 14.97/6.88  tff(c_38336, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38307, c_33865])).
% 14.97/6.88  tff(c_38628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_38325, c_38336])).
% 14.97/6.88  tff(c_38629, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_33874])).
% 14.97/6.88  tff(c_38632, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38629, c_33846])).
% 14.97/6.88  tff(c_43094, plain, (![A_2517, B_2518, C_2519]: (k1_relset_1(A_2517, B_2518, C_2519)=k1_relat_1(C_2519) | ~m1_subset_1(C_2519, k1_zfmisc_1(k2_zfmisc_1(A_2517, B_2518))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.97/6.88  tff(c_43125, plain, (![C_2522]: (k1_relset_1('#skF_2', '#skF_1', C_2522)=k1_relat_1(C_2522) | ~m1_subset_1(C_2522, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_38629, c_43094])).
% 14.97/6.88  tff(c_43133, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_38632, c_43125])).
% 14.97/6.88  tff(c_44968, plain, (![B_2641, C_2642, A_2643]: (k1_xboole_0=B_2641 | v1_funct_2(C_2642, A_2643, B_2641) | k1_relset_1(A_2643, B_2641, C_2642)!=A_2643 | ~m1_subset_1(C_2642, k1_zfmisc_1(k2_zfmisc_1(A_2643, B_2641))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_44977, plain, (![C_2642]: (k1_xboole_0='#skF_1' | v1_funct_2(C_2642, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_2642)!='#skF_2' | ~m1_subset_1(C_2642, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_38629, c_44968])).
% 14.97/6.88  tff(c_45046, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_44977])).
% 14.97/6.88  tff(c_38643, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38629, c_8])).
% 14.97/6.88  tff(c_38681, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38643])).
% 14.97/6.88  tff(c_45073, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45046, c_38681])).
% 14.97/6.88  tff(c_45079, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45046, c_45046, c_10])).
% 14.97/6.88  tff(c_45309, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45079, c_38629])).
% 14.97/6.88  tff(c_45311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45073, c_45309])).
% 14.97/6.88  tff(c_46028, plain, (![C_2711]: (v1_funct_2(C_2711, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_2711)!='#skF_2' | ~m1_subset_1(C_2711, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_44977])).
% 14.97/6.88  tff(c_46031, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_38632, c_46028])).
% 14.97/6.88  tff(c_46037, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_43133, c_46031])).
% 14.97/6.88  tff(c_46038, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_33845, c_46037])).
% 14.97/6.88  tff(c_46042, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_46038])).
% 14.97/6.88  tff(c_46045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_43198, c_46042])).
% 14.97/6.88  tff(c_46046, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_38643])).
% 14.97/6.88  tff(c_46110, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_46046])).
% 14.97/6.88  tff(c_42, plain, (![A_25]: (v1_funct_2(k1_xboole_0, A_25, k1_xboole_0) | k1_xboole_0=A_25 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_25, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_74, plain, (![A_25]: (v1_funct_2(k1_xboole_0, A_25, k1_xboole_0) | k1_xboole_0=A_25 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_42])).
% 14.97/6.88  tff(c_46130, plain, (![A_25]: (v1_funct_2('#skF_1', A_25, '#skF_1') | A_25='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46110, c_46110, c_46110, c_46110, c_46110, c_74])).
% 14.97/6.88  tff(c_46131, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_46130])).
% 14.97/6.88  tff(c_46219, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_16, c_46131])).
% 14.97/6.88  tff(c_46223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_46219])).
% 14.97/6.88  tff(c_46225, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_46130])).
% 14.97/6.88  tff(c_46, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_72, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 14.97/6.88  tff(c_46771, plain, (![C_2757, B_2758]: (v1_funct_2(C_2757, '#skF_1', B_2758) | k1_relset_1('#skF_1', B_2758, C_2757)!='#skF_1' | ~m1_subset_1(C_2757, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46110, c_46110, c_46110, c_46110, c_72])).
% 14.97/6.88  tff(c_46937, plain, (![B_2771]: (v1_funct_2('#skF_1', '#skF_1', B_2771) | k1_relset_1('#skF_1', B_2771, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_46225, c_46771])).
% 14.97/6.88  tff(c_46443, plain, (![A_2728]: (v1_funct_2('#skF_1', A_2728, '#skF_1') | A_2728='#skF_1')), inference(splitRight, [status(thm)], [c_46130])).
% 14.97/6.88  tff(c_46047, plain, (k2_funct_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_38643])).
% 14.97/6.88  tff(c_46053, plain, (~v1_funct_2(k1_xboole_0, '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46047, c_33845])).
% 14.97/6.88  tff(c_46115, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46110, c_46053])).
% 14.97/6.88  tff(c_46447, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_46443, c_46115])).
% 14.97/6.88  tff(c_46448, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46447, c_46115])).
% 14.97/6.88  tff(c_46953, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_46937, c_46448])).
% 14.97/6.88  tff(c_46117, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46110, c_46047])).
% 14.97/6.88  tff(c_46377, plain, (![A_2726]: (k1_relat_1(k2_funct_1(A_2726))=k2_relat_1(A_2726) | ~v2_funct_1(A_2726) | ~v1_funct_1(A_2726) | ~v1_relat_1(A_2726))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.97/6.88  tff(c_46389, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46117, c_46377])).
% 14.97/6.88  tff(c_46393, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_46389])).
% 14.97/6.88  tff(c_46125, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46110, c_46110, c_12])).
% 14.97/6.88  tff(c_46255, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46125, c_66])).
% 14.97/6.88  tff(c_46123, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46110, c_46110, c_10])).
% 14.97/6.88  tff(c_46456, plain, (![A_2729, B_2730, C_2731]: (k2_relset_1(A_2729, B_2730, C_2731)=k2_relat_1(C_2731) | ~m1_subset_1(C_2731, k1_zfmisc_1(k2_zfmisc_1(A_2729, B_2730))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.97/6.88  tff(c_47211, plain, (![A_2787, C_2788]: (k2_relset_1(A_2787, '#skF_1', C_2788)=k2_relat_1(C_2788) | ~m1_subset_1(C_2788, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_46123, c_46456])).
% 14.97/6.88  tff(c_47213, plain, (![A_2787]: (k2_relset_1(A_2787, '#skF_1', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_46255, c_47211])).
% 14.97/6.88  tff(c_47224, plain, (![A_2789]: (k2_relset_1(A_2789, '#skF_1', '#skF_3')=k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46393, c_47213])).
% 14.97/6.88  tff(c_46450, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46447, c_46447, c_62])).
% 14.97/6.88  tff(c_47228, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_47224, c_46450])).
% 14.97/6.88  tff(c_78, plain, (![B_32]: (k2_zfmisc_1(k1_xboole_0, B_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.97/6.88  tff(c_82, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78, c_24])).
% 14.97/6.88  tff(c_46124, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46110, c_82])).
% 14.97/6.88  tff(c_46048, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46047, c_46047, c_38632])).
% 14.97/6.88  tff(c_46099, plain, (![B_4]: (v5_relat_1(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_46048, c_187])).
% 14.97/6.88  tff(c_46112, plain, (![B_4]: (v5_relat_1('#skF_1', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_46110, c_46099])).
% 14.97/6.88  tff(c_46281, plain, (![A_2723]: (k2_relat_1(k2_funct_1(A_2723))=k1_relat_1(A_2723) | ~v2_funct_1(A_2723) | ~v1_funct_1(A_2723) | ~v1_relat_1(A_2723))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.97/6.88  tff(c_46302, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46117, c_46281])).
% 14.97/6.88  tff(c_46306, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_46302])).
% 14.97/6.88  tff(c_46351, plain, (![A_10]: (r1_tarski(k1_relat_1('#skF_3'), A_10) | ~v5_relat_1('#skF_1', A_10) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46306, c_22])).
% 14.97/6.88  tff(c_46363, plain, (![A_10]: (r1_tarski(k1_relat_1('#skF_3'), A_10))), inference(demodulation, [status(thm), theory('equality')], [c_46124, c_46112, c_46351])).
% 14.97/6.88  tff(c_46549, plain, (![C_2741, B_2742]: (v5_relat_1(C_2741, B_2742) | ~m1_subset_1(C_2741, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46110, c_187])).
% 14.97/6.88  tff(c_46557, plain, (![B_2742]: (v5_relat_1('#skF_3', B_2742))), inference(resolution, [status(thm)], [c_46255, c_46549])).
% 14.97/6.88  tff(c_46400, plain, (![A_10]: (r1_tarski(k1_relat_1('#skF_1'), A_10) | ~v5_relat_1('#skF_3', A_10) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_46393, c_22])).
% 14.97/6.88  tff(c_46412, plain, (![A_10]: (r1_tarski(k1_relat_1('#skF_1'), A_10) | ~v5_relat_1('#skF_3', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_46400])).
% 14.97/6.88  tff(c_46566, plain, (![A_2744]: (r1_tarski(k1_relat_1('#skF_1'), A_2744))), inference(demodulation, [status(thm), theory('equality')], [c_46557, c_46412])).
% 14.97/6.88  tff(c_46603, plain, (![A_2748]: (k1_relat_1('#skF_1')=A_2748 | ~r1_tarski(A_2748, k1_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_46566, c_2])).
% 14.97/6.88  tff(c_46622, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_46363, c_46603])).
% 14.97/6.88  tff(c_46054, plain, (v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46047, c_162])).
% 14.97/6.88  tff(c_46116, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46110, c_46054])).
% 14.97/6.88  tff(c_46496, plain, (![A_2737]: (m1_subset_1(A_2737, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_2737), k2_relat_1(A_2737)))) | ~v1_funct_1(A_2737) | ~v1_relat_1(A_2737))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.97/6.88  tff(c_46520, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_relat_1('#skF_3')))) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_46306, c_46496])).
% 14.97/6.88  tff(c_46534, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46124, c_46116, c_46520])).
% 14.97/6.88  tff(c_46847, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_relat_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46622, c_46534])).
% 14.97/6.88  tff(c_38, plain, (![A_19, B_20, C_21]: (k1_relset_1(A_19, B_20, C_21)=k1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.97/6.88  tff(c_46866, plain, (k1_relset_1(k1_relat_1('#skF_1'), k1_relat_1('#skF_1'), '#skF_1')=k1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_46847, c_38])).
% 14.97/6.88  tff(c_47241, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47228, c_47228, c_47228, c_46866])).
% 14.97/6.88  tff(c_47262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46953, c_47241])).
% 14.97/6.88  tff(c_47263, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_46046])).
% 14.97/6.88  tff(c_47264, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_46046])).
% 14.97/6.88  tff(c_47285, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47263, c_47264])).
% 14.97/6.88  tff(c_47278, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47263, c_47263, c_10])).
% 14.97/6.88  tff(c_47415, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_47278, c_66])).
% 14.97/6.88  tff(c_44, plain, (![C_27, A_25]: (k1_xboole_0=C_27 | ~v1_funct_2(C_27, A_25, k1_xboole_0) | k1_xboole_0=A_25 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_73, plain, (![C_27, A_25]: (k1_xboole_0=C_27 | ~v1_funct_2(C_27, A_25, k1_xboole_0) | k1_xboole_0=A_25 | ~m1_subset_1(C_27, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_44])).
% 14.97/6.88  tff(c_47554, plain, (![C_2801, A_2802]: (C_2801='#skF_2' | ~v1_funct_2(C_2801, A_2802, '#skF_2') | A_2802='#skF_2' | ~m1_subset_1(C_2801, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_47263, c_47263, c_47263, c_47263, c_73])).
% 14.97/6.88  tff(c_47556, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_47554])).
% 14.97/6.88  tff(c_47559, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47415, c_47556])).
% 14.97/6.88  tff(c_47560, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_47285, c_47559])).
% 14.97/6.88  tff(c_47413, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47278, c_33865])).
% 14.97/6.88  tff(c_47569, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47560, c_47413])).
% 14.97/6.88  tff(c_47587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_47569])).
% 14.97/6.88  tff(c_47588, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_126])).
% 14.97/6.88  tff(c_47591, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_47588, c_66])).
% 14.97/6.88  tff(c_48795, plain, (![A_2924, B_2925, C_2926]: (k2_relset_1(A_2924, B_2925, C_2926)=k2_relat_1(C_2926) | ~m1_subset_1(C_2926, k1_zfmisc_1(k2_zfmisc_1(A_2924, B_2925))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.97/6.88  tff(c_48849, plain, (![C_2931]: (k2_relset_1('#skF_1', '#skF_2', C_2931)=k2_relat_1(C_2931) | ~m1_subset_1(C_2931, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_47588, c_48795])).
% 14.97/6.88  tff(c_48852, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_47591, c_48849])).
% 14.97/6.88  tff(c_48858, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_48852])).
% 14.97/6.88  tff(c_48921, plain, (![A_2933, B_2934, C_2935]: (k1_relset_1(A_2933, B_2934, C_2935)=k1_relat_1(C_2935) | ~m1_subset_1(C_2935, k1_zfmisc_1(k2_zfmisc_1(A_2933, B_2934))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.97/6.88  tff(c_48938, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_33846, c_48921])).
% 14.97/6.88  tff(c_49644, plain, (![B_3006, C_3007, A_3008]: (k1_xboole_0=B_3006 | v1_funct_2(C_3007, A_3008, B_3006) | k1_relset_1(A_3008, B_3006, C_3007)!=A_3008 | ~m1_subset_1(C_3007, k1_zfmisc_1(k2_zfmisc_1(A_3008, B_3006))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.97/6.88  tff(c_49656, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_33846, c_49644])).
% 14.97/6.88  tff(c_49672, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48938, c_49656])).
% 14.97/6.88  tff(c_49673, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_33845, c_49672])).
% 14.97/6.88  tff(c_49676, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_49673])).
% 14.97/6.88  tff(c_49679, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_49676])).
% 14.97/6.88  tff(c_49682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_48858, c_49679])).
% 14.97/6.88  tff(c_49683, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_49673])).
% 14.97/6.88  tff(c_47602, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_47588, c_8])).
% 14.97/6.88  tff(c_47630, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_47602])).
% 14.97/6.88  tff(c_49727, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_49683, c_47630])).
% 14.97/6.88  tff(c_49731, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49683, c_49683, c_12])).
% 14.97/6.88  tff(c_49811, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_49731, c_47588])).
% 14.97/6.88  tff(c_49813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49727, c_49811])).
% 14.97/6.88  tff(c_49815, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_47602])).
% 14.97/6.88  tff(c_49942, plain, (![C_3026, B_3027]: (v5_relat_1(C_3026, B_3027) | ~m1_subset_1(C_3026, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_49815, c_187])).
% 14.97/6.88  tff(c_49948, plain, (![B_3027]: (v5_relat_1('#skF_3', B_3027))), inference(resolution, [status(thm)], [c_47591, c_49942])).
% 14.97/6.88  tff(c_49819, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_49815, c_49815, c_10])).
% 14.97/6.88  tff(c_50250, plain, (![A_3068, B_3069, C_3070]: (k2_relset_1(A_3068, B_3069, C_3070)=k2_relat_1(C_3070) | ~m1_subset_1(C_3070, k1_zfmisc_1(k2_zfmisc_1(A_3068, B_3069))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.97/6.88  tff(c_50274, plain, (![A_3075, C_3076]: (k2_relset_1(A_3075, '#skF_3', C_3076)=k2_relat_1(C_3076) | ~m1_subset_1(C_3076, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_49819, c_50250])).
% 14.97/6.88  tff(c_50285, plain, (![A_3077]: (k2_relset_1(A_3077, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_47591, c_50274])).
% 14.97/6.88  tff(c_49814, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_47602])).
% 14.97/6.88  tff(c_49827, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_49815, c_49815, c_49814])).
% 14.97/6.88  tff(c_49828, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_49827])).
% 14.97/6.88  tff(c_49835, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_49828, c_49828, c_62])).
% 14.97/6.88  tff(c_50289, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_50285, c_49835])).
% 14.97/6.88  tff(c_50341, plain, (![A_10]: (r1_tarski('#skF_3', A_10) | ~v5_relat_1('#skF_3', A_10) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_50289, c_22])).
% 14.97/6.88  tff(c_50359, plain, (![A_10]: (r1_tarski('#skF_3', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_49948, c_50341])).
% 14.97/6.88  tff(c_49821, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_49815, c_49815, c_12])).
% 14.97/6.88  tff(c_47629, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_33864, c_2])).
% 14.97/6.88  tff(c_49981, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_49821, c_49828, c_49821, c_49828, c_47629])).
% 14.97/6.88  tff(c_49982, plain, (~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_49981])).
% 14.97/6.88  tff(c_50364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50359, c_49982])).
% 14.97/6.88  tff(c_50365, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_49981])).
% 14.97/6.88  tff(c_49829, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_49828, c_33864])).
% 14.97/6.88  tff(c_49906, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_49821, c_49829])).
% 14.97/6.88  tff(c_49915, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_49906, c_2])).
% 14.97/6.88  tff(c_49980, plain, (~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_49915])).
% 14.97/6.88  tff(c_50396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_50365, c_49980])).
% 14.97/6.88  tff(c_50397, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_49915])).
% 14.97/6.88  tff(c_50427, plain, (![A_3081]: (k1_relat_1(k2_funct_1(A_3081))=k2_relat_1(A_3081) | ~v2_funct_1(A_3081) | ~v1_funct_1(A_3081) | ~v1_relat_1(A_3081))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.97/6.88  tff(c_50439, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50397, c_50427])).
% 14.97/6.88  tff(c_50443, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70, c_64, c_50439])).
% 14.97/6.88  tff(c_50834, plain, (![A_3112, B_3113, C_3114]: (k2_relset_1(A_3112, B_3113, C_3114)=k2_relat_1(C_3114) | ~m1_subset_1(C_3114, k1_zfmisc_1(k2_zfmisc_1(A_3112, B_3113))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.97/6.88  tff(c_50846, plain, (![A_3115, C_3116]: (k2_relset_1(A_3115, '#skF_3', C_3116)=k2_relat_1(C_3116) | ~m1_subset_1(C_3116, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_49819, c_50834])).
% 14.97/6.88  tff(c_50848, plain, (![A_3115]: (k2_relset_1(A_3115, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_47591, c_50846])).
% 14.97/6.88  tff(c_50855, plain, (![A_3117]: (k2_relset_1(A_3117, '#skF_3', '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50443, c_50848])).
% 14.97/6.88  tff(c_50859, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_50855, c_49835])).
% 14.97/6.88  tff(c_50456, plain, (![A_10]: (r1_tarski(k1_relat_1('#skF_3'), A_10) | ~v5_relat_1('#skF_3', A_10) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_50443, c_22])).
% 14.97/6.88  tff(c_50466, plain, (![A_10]: (r1_tarski(k1_relat_1('#skF_3'), A_10))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_49948, c_50456])).
% 14.97/6.88  tff(c_50878, plain, (![A_10]: (r1_tarski('#skF_3', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_50859, c_50466])).
% 14.97/6.88  tff(c_50948, plain, (![A_3119, B_3120, C_3121]: (k1_relset_1(A_3119, B_3120, C_3121)=k1_relat_1(C_3121) | ~m1_subset_1(C_3121, k1_zfmisc_1(k2_zfmisc_1(A_3119, B_3120))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.97/6.88  tff(c_51284, plain, (![A_3149, B_3150, A_3151]: (k1_relset_1(A_3149, B_3150, A_3151)=k1_relat_1(A_3151) | ~r1_tarski(A_3151, k2_zfmisc_1(A_3149, B_3150)))), inference(resolution, [status(thm)], [c_16, c_50948])).
% 14.97/6.88  tff(c_51291, plain, (![A_3149, B_3150]: (k1_relset_1(A_3149, B_3150, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_50878, c_51284])).
% 14.97/6.88  tff(c_51308, plain, (![A_3149, B_3150]: (k1_relset_1(A_3149, B_3150, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50859, c_51291])).
% 14.97/6.88  tff(c_51338, plain, (![C_3156, B_3157]: (v1_funct_2(C_3156, '#skF_3', B_3157) | k1_relset_1('#skF_3', B_3157, C_3156)!='#skF_3' | ~m1_subset_1(C_3156, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_49815, c_49815, c_49815, c_49815, c_72])).
% 14.97/6.88  tff(c_51340, plain, (![B_3157]: (v1_funct_2('#skF_3', '#skF_3', B_3157) | k1_relset_1('#skF_3', B_3157, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_47591, c_51338])).
% 14.97/6.88  tff(c_51346, plain, (![B_3157]: (v1_funct_2('#skF_3', '#skF_3', B_3157))), inference(demodulation, [status(thm), theory('equality')], [c_51308, c_51340])).
% 14.97/6.88  tff(c_49833, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49828, c_33845])).
% 14.97/6.88  tff(c_50403, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50397, c_49833])).
% 14.97/6.88  tff(c_51351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51346, c_50403])).
% 14.97/6.88  tff(c_51352, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_49827])).
% 14.97/6.88  tff(c_51353, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_49827])).
% 14.97/6.88  tff(c_51375, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_51353])).
% 14.97/6.88  tff(c_51366, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_152])).
% 14.97/6.88  tff(c_51370, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_70])).
% 14.97/6.88  tff(c_51369, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_64])).
% 14.97/6.88  tff(c_51360, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_33863])).
% 14.97/6.88  tff(c_51386, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_51352, c_49819])).
% 14.97/6.88  tff(c_51361, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_33846])).
% 14.97/6.88  tff(c_51457, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_51386, c_51361])).
% 14.97/6.88  tff(c_51354, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_49815])).
% 14.97/6.88  tff(c_51518, plain, (![C_3175, B_3176]: (v5_relat_1(C_3175, B_3176) | ~m1_subset_1(C_3175, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_51354, c_187])).
% 14.97/6.88  tff(c_51526, plain, (![B_3176]: (v5_relat_1(k2_funct_1('#skF_1'), B_3176))), inference(resolution, [status(thm)], [c_51457, c_51518])).
% 14.97/6.88  tff(c_51356, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_51352, c_47591])).
% 14.97/6.88  tff(c_51527, plain, (![B_3176]: (v5_relat_1('#skF_1', B_3176))), inference(resolution, [status(thm)], [c_51356, c_51518])).
% 14.97/6.88  tff(c_51414, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_51352, c_49821])).
% 14.97/6.88  tff(c_51722, plain, (![A_3203, B_3204, C_3205]: (k2_relset_1(A_3203, B_3204, C_3205)=k2_relat_1(C_3205) | ~m1_subset_1(C_3205, k1_zfmisc_1(k2_zfmisc_1(A_3203, B_3204))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.97/6.88  tff(c_51738, plain, (![B_3207, C_3208]: (k2_relset_1('#skF_1', B_3207, C_3208)=k2_relat_1(C_3208) | ~m1_subset_1(C_3208, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_51414, c_51722])).
% 14.97/6.88  tff(c_51749, plain, (![B_3209]: (k2_relset_1('#skF_1', B_3209, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_51356, c_51738])).
% 14.97/6.88  tff(c_51367, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_62])).
% 14.97/6.88  tff(c_51753, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_51749, c_51367])).
% 14.97/6.88  tff(c_51774, plain, (![A_10]: (r1_tarski('#skF_2', A_10) | ~v5_relat_1('#skF_1', A_10) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51753, c_22])).
% 14.97/6.88  tff(c_51793, plain, (![A_3210]: (r1_tarski('#skF_2', A_3210))), inference(demodulation, [status(thm), theory('equality')], [c_51366, c_51527, c_51774])).
% 14.97/6.88  tff(c_51835, plain, (![A_3216]: (A_3216='#skF_2' | ~r1_tarski(A_3216, '#skF_2'))), inference(resolution, [status(thm)], [c_51793, c_2])).
% 14.97/6.88  tff(c_51875, plain, (![B_3218]: (k2_relat_1(B_3218)='#skF_2' | ~v5_relat_1(B_3218, '#skF_2') | ~v1_relat_1(B_3218))), inference(resolution, [status(thm)], [c_22, c_51835])).
% 14.97/6.88  tff(c_51891, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_51526, c_51875])).
% 14.97/6.88  tff(c_51905, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_51360, c_51891])).
% 14.97/6.88  tff(c_51961, plain, (k1_relat_1('#skF_1')='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_51905, c_30])).
% 14.97/6.88  tff(c_51982, plain, (k1_relat_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_51366, c_51370, c_51369, c_51961])).
% 14.97/6.88  tff(c_51909, plain, (![A_3219, B_3220, C_3221]: (k1_relset_1(A_3219, B_3220, C_3221)=k1_relat_1(C_3221) | ~m1_subset_1(C_3221, k1_zfmisc_1(k2_zfmisc_1(A_3219, B_3220))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.97/6.88  tff(c_52423, plain, (![B_3237, C_3238]: (k1_relset_1('#skF_1', B_3237, C_3238)=k1_relat_1(C_3238) | ~m1_subset_1(C_3238, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_51414, c_51909])).
% 14.97/6.88  tff(c_52427, plain, (![B_3237]: (k1_relset_1('#skF_1', B_3237, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_51356, c_52423])).
% 14.97/6.88  tff(c_52436, plain, (![B_3239]: (k1_relset_1('#skF_1', B_3239, '#skF_1')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51982, c_52427])).
% 14.97/6.88  tff(c_51368, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51352, c_68])).
% 14.97/6.88  tff(c_52196, plain, (![B_3227, C_3228]: (k1_relset_1('#skF_1', B_3227, C_3228)='#skF_1' | ~v1_funct_2(C_3228, '#skF_1', B_3227) | ~m1_subset_1(C_3228, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_51354, c_51354, c_51354, c_51354, c_71])).
% 14.97/6.88  tff(c_52201, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_51368, c_52196])).
% 14.97/6.88  tff(c_52208, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_51356, c_52201])).
% 14.97/6.88  tff(c_52440, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_52436, c_52208])).
% 14.97/6.88  tff(c_52447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51375, c_52440])).
% 14.97/6.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.97/6.88  
% 14.97/6.88  Inference rules
% 14.97/6.88  ----------------------
% 14.97/6.88  #Ref     : 0
% 14.97/6.88  #Sup     : 10587
% 14.97/6.88  #Fact    : 0
% 14.97/6.88  #Define  : 0
% 14.97/6.88  #Split   : 279
% 14.97/6.88  #Chain   : 0
% 14.97/6.88  #Close   : 0
% 14.97/6.88  
% 14.97/6.88  Ordering : KBO
% 14.97/6.88  
% 14.97/6.88  Simplification rules
% 14.97/6.88  ----------------------
% 14.97/6.88  #Subsume      : 3522
% 14.97/6.88  #Demod        : 13837
% 14.97/6.88  #Tautology    : 5536
% 14.97/6.88  #SimpNegUnit  : 1379
% 14.97/6.88  #BackRed      : 2208
% 14.97/6.88  
% 14.97/6.88  #Partial instantiations: 0
% 14.97/6.88  #Strategies tried      : 1
% 14.97/6.88  
% 14.97/6.88  Timing (in seconds)
% 14.97/6.88  ----------------------
% 14.97/6.89  Preprocessing        : 0.33
% 14.97/6.89  Parsing              : 0.17
% 14.97/6.89  CNF conversion       : 0.02
% 14.97/6.89  Main loop            : 5.50
% 14.97/6.89  Inferencing          : 1.61
% 14.97/6.89  Reduction            : 2.16
% 14.97/6.89  Demodulation         : 1.58
% 14.97/6.89  BG Simplification    : 0.14
% 14.97/6.89  Subsumption          : 1.19
% 14.97/6.89  Abstraction          : 0.19
% 14.97/6.89  MUC search           : 0.00
% 14.97/6.89  Cooper               : 0.00
% 14.97/6.89  Total                : 6.02
% 14.97/6.89  Index Insertion      : 0.00
% 14.97/6.89  Index Deletion       : 0.00
% 14.97/6.89  Index Matching       : 0.00
% 14.97/6.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
