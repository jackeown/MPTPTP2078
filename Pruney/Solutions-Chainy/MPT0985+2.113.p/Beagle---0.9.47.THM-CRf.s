%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:44 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :  213 (1822 expanded)
%              Number of leaves         :   43 ( 605 expanded)
%              Depth                    :   16
%              Number of atoms          :  373 (5026 expanded)
%              Number of equality atoms :  168 (1793 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_140,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_150,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_3282,plain,(
    ! [C_269,A_270,B_271] :
      ( v1_relat_1(C_269)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3298,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3282])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_3576,plain,(
    ! [A_302,B_303,C_304] :
      ( k2_relset_1(A_302,B_303,C_304) = k2_relat_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3588,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3576])).

tff(c_3604,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3588])).

tff(c_46,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_197,plain,(
    ! [A_46] :
      ( v1_funct_1(k2_funct_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_183,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_200,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_197,c_183])).

tff(c_203,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_200])).

tff(c_300,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_303,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_300])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_303])).

tff(c_316,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_391,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_480,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_492,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_480])).

tff(c_32,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_684,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(A_98,B_99,C_100) = k2_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_693,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_684])).

tff(c_708,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_693])).

tff(c_22,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_501,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_492,c_22])).

tff(c_518,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_710,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_518])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_627,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_645,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_627])).

tff(c_1300,plain,(
    ! [B_143,A_144,C_145] :
      ( k1_xboole_0 = B_143
      | k1_relset_1(A_144,B_143,C_145) = A_144
      | ~ v1_funct_2(C_145,A_144,B_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1315,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1300])).

tff(c_1335,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_645,c_1315])).

tff(c_1336,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_710,c_1335])).

tff(c_541,plain,(
    ! [A_81] :
      ( k2_relat_1(k2_funct_1(A_81)) = k1_relat_1(A_81)
      | ~ v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_20,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1565,plain,(
    ! [A_160] :
      ( k10_relat_1(k2_funct_1(A_160),k1_relat_1(A_160)) = k1_relat_1(k2_funct_1(A_160))
      | ~ v1_relat_1(k2_funct_1(A_160))
      | ~ v2_funct_1(A_160)
      | ~ v1_funct_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_20])).

tff(c_1577,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_1565])).

tff(c_1591,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_82,c_76,c_1577])).

tff(c_1599,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1591])).

tff(c_1602,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1599])).

tff(c_1606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_82,c_1602])).

tff(c_1608,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1591])).

tff(c_317,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_18,plain,(
    ! [A_7] :
      ( k9_relat_1(A_7,k1_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1367,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1336,c_18])).

tff(c_1379,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_708,c_1367])).

tff(c_1607,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1591])).

tff(c_40,plain,(
    ! [B_16,A_15] :
      ( k10_relat_1(k2_funct_1(B_16),A_15) = k9_relat_1(B_16,A_15)
      | ~ v2_funct_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1620,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1607,c_40])).

tff(c_1627,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_82,c_76,c_1379,c_1620])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_17,B_19] :
      ( k9_relat_1(k2_funct_1(A_17),k9_relat_1(A_17,B_19)) = B_19
      | ~ r1_tarski(B_19,k1_relat_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1397,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1379,c_42])).

tff(c_1401,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_82,c_76,c_6,c_1336,c_1397])).

tff(c_1656,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1627,c_18])).

tff(c_1677,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1608,c_1401,c_1656])).

tff(c_66,plain,(
    ! [A_33] :
      ( m1_subset_1(A_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33),k2_relat_1(A_33))))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1699,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1677,c_66])).

tff(c_1728,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1608,c_317,c_1627,c_1699])).

tff(c_1730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_1728])).

tff(c_1731,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_28,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_149,plain,(
    ! [A_44] :
      ( k2_relat_1(A_44) != k1_xboole_0
      | k1_xboole_0 = A_44
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_152,plain,(
    ! [A_12] :
      ( k2_relat_1(k6_relat_1(A_12)) != k1_xboole_0
      | k6_relat_1(A_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_149])).

tff(c_156,plain,(
    ! [A_45] :
      ( k1_xboole_0 != A_45
      | k6_relat_1(A_45) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_152])).

tff(c_26,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_165,plain,(
    ! [A_45] :
      ( k1_relat_1(k1_xboole_0) = A_45
      | k1_xboole_0 != A_45 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_26])).

tff(c_1841,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1731,c_1731,c_165])).

tff(c_24,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_500,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_492,c_24])).

tff(c_502,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_1733,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1731,c_502])).

tff(c_1845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1841,c_1733])).

tff(c_1846,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1860,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1846,c_1846,c_12])).

tff(c_162,plain,(
    ! [A_45] :
      ( k2_relat_1(k1_xboole_0) = A_45
      | k1_xboole_0 != A_45 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_28])).

tff(c_1957,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1846,c_1846,c_162])).

tff(c_2152,plain,(
    ! [A_186,B_187,C_188] :
      ( k2_relset_1(A_186,B_187,C_188) = k2_relat_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2164,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2152])).

tff(c_2171,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_74,c_2164])).

tff(c_2174,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2171,c_391])).

tff(c_2178,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1860,c_2174])).

tff(c_154,plain,(
    ! [A_12] :
      ( k1_xboole_0 != A_12
      | k6_relat_1(A_12) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_152])).

tff(c_1856,plain,(
    ! [A_12] :
      ( A_12 != '#skF_3'
      | k6_relat_1(A_12) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1846,c_1846,c_154])).

tff(c_36,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_425,plain,(
    ! [A_68] :
      ( k9_relat_1(A_68,k1_relat_1(A_68)) = k2_relat_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_434,plain,(
    ! [A_10] :
      ( k9_relat_1(k6_relat_1(A_10),A_10) = k2_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_425])).

tff(c_438,plain,(
    ! [A_10] : k9_relat_1(k6_relat_1(A_10),A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_434])).

tff(c_2764,plain,(
    ! [A_244,B_245] :
      ( k9_relat_1(k2_funct_1(A_244),k9_relat_1(A_244,B_245)) = B_245
      | ~ r1_tarski(B_245,k1_relat_1(A_244))
      | ~ v2_funct_1(A_244)
      | ~ v1_funct_1(A_244)
      | ~ v1_relat_1(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2782,plain,(
    ! [A_10] :
      ( k9_relat_1(k2_funct_1(k6_relat_1(A_10)),A_10) = A_10
      | ~ r1_tarski(A_10,k1_relat_1(k6_relat_1(A_10)))
      | ~ v2_funct_1(k6_relat_1(A_10))
      | ~ v1_funct_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_2764])).

tff(c_2794,plain,(
    ! [A_246] :
      ( k9_relat_1(k2_funct_1(k6_relat_1(A_246)),A_246) = A_246
      | ~ v1_funct_1(k6_relat_1(A_246)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_6,c_26,c_2782])).

tff(c_2845,plain,(
    ! [A_248] :
      ( k9_relat_1(k2_funct_1('#skF_3'),A_248) = A_248
      | ~ v1_funct_1(k6_relat_1(A_248))
      | A_248 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1856,c_2794])).

tff(c_2848,plain,(
    ! [A_12] :
      ( k9_relat_1(k2_funct_1('#skF_3'),A_12) = A_12
      | ~ v1_funct_1('#skF_3')
      | A_12 != '#skF_3'
      | A_12 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1856,c_2845])).

tff(c_2852,plain,(
    ! [A_249] :
      ( k9_relat_1(k2_funct_1('#skF_3'),A_249) = A_249
      | A_249 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2848])).

tff(c_2877,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2852])).

tff(c_3082,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2877])).

tff(c_3128,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3082])).

tff(c_3132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_82,c_3128])).

tff(c_3134,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2877])).

tff(c_2866,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2852,c_18])).

tff(c_3145,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3134,c_2866])).

tff(c_3146,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3145])).

tff(c_3149,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3146])).

tff(c_3152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_82,c_76,c_1957,c_3149])).

tff(c_3154,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3145])).

tff(c_3167,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3154,c_66])).

tff(c_3190,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3134,c_317,c_1860,c_3167])).

tff(c_3192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2178,c_3190])).

tff(c_3193,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_3194,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_3428,plain,(
    ! [A_285,B_286,C_287] :
      ( k1_relset_1(A_285,B_286,C_287) = k1_relat_1(C_287)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3445,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3194,c_3428])).

tff(c_3893,plain,(
    ! [B_329,C_330,A_331] :
      ( k1_xboole_0 = B_329
      | v1_funct_2(C_330,A_331,B_329)
      | k1_relset_1(A_331,B_329,C_330) != A_331
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_331,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3908,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3194,c_3893])).

tff(c_3930,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3445,c_3908])).

tff(c_3931,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3193,c_3930])).

tff(c_3953,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3931])).

tff(c_3956,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3953])).

tff(c_3959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_82,c_76,c_3604,c_3956])).

tff(c_3960,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3931])).

tff(c_3306,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3298,c_24])).

tff(c_3331,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3306])).

tff(c_3988,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3960,c_3331])).

tff(c_4001,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3960,c_3960,c_12])).

tff(c_4112,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4001,c_78])).

tff(c_3444,plain,(
    ! [B_4,C_287] :
      ( k1_relset_1(k1_xboole_0,B_4,C_287) = k1_relat_1(C_287)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3428])).

tff(c_4612,plain,(
    ! [B_364,C_365] :
      ( k1_relset_1('#skF_1',B_364,C_365) = k1_relat_1(C_365)
      | ~ m1_subset_1(C_365,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3960,c_3960,c_3444])).

tff(c_4620,plain,(
    ! [B_364] : k1_relset_1('#skF_1',B_364,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4112,c_4612])).

tff(c_62,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1(k1_xboole_0,B_31,C_32) = k1_xboole_0
      | ~ v1_funct_2(C_32,k1_xboole_0,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_84,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1(k1_xboole_0,B_31,C_32) = k1_xboole_0
      | ~ v1_funct_2(C_32,k1_xboole_0,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_62])).

tff(c_5089,plain,(
    ! [B_396,C_397] :
      ( k1_relset_1('#skF_1',B_396,C_397) = '#skF_1'
      | ~ v1_funct_2(C_397,'#skF_1',B_396)
      | ~ m1_subset_1(C_397,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3960,c_3960,c_3960,c_3960,c_84])).

tff(c_5102,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_5089])).

tff(c_5118,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4112,c_4620,c_5102])).

tff(c_5120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3988,c_5118])).

tff(c_5121,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3306])).

tff(c_5122,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3306])).

tff(c_5142,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5121,c_5122])).

tff(c_5135,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5121,c_5121,c_12])).

tff(c_14,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_5424,plain,(
    ! [A_412,B_413,C_414] :
      ( k1_relset_1(A_412,B_413,C_414) = k1_relat_1(C_414)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_5795,plain,(
    ! [A_443,B_444] : k1_relset_1(A_443,B_444,k2_zfmisc_1(A_443,B_444)) = k1_relat_1(k2_zfmisc_1(A_443,B_444)) ),
    inference(resolution,[status(thm)],[c_83,c_5424])).

tff(c_5804,plain,(
    ! [B_4] : k1_relat_1(k2_zfmisc_1('#skF_3',B_4)) = k1_relset_1('#skF_3',B_4,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5135,c_5795])).

tff(c_5810,plain,(
    ! [B_4] : k1_relset_1('#skF_3',B_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5142,c_5135,c_5804])).

tff(c_58,plain,(
    ! [C_32,B_31] :
      ( v1_funct_2(C_32,k1_xboole_0,B_31)
      | k1_relset_1(k1_xboole_0,B_31,C_32) != k1_xboole_0
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_85,plain,(
    ! [C_32,B_31] :
      ( v1_funct_2(C_32,k1_xboole_0,B_31)
      | k1_relset_1(k1_xboole_0,B_31,C_32) != k1_xboole_0
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_58])).

tff(c_5950,plain,(
    ! [C_454,B_455] :
      ( v1_funct_2(C_454,'#skF_3',B_455)
      | k1_relset_1('#skF_3',B_455,C_454) != '#skF_3'
      | ~ m1_subset_1(C_454,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5121,c_5121,c_5121,c_5121,c_85])).

tff(c_5953,plain,(
    ! [B_455] :
      ( v1_funct_2('#skF_3','#skF_3',B_455)
      | k1_relset_1('#skF_3',B_455,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_83,c_5950])).

tff(c_5956,plain,(
    ! [B_455] : v1_funct_2('#skF_3','#skF_3',B_455) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5810,c_5953])).

tff(c_5200,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5121,c_5121,c_162])).

tff(c_5454,plain,(
    ! [A_415,B_416,C_417] :
      ( k2_relset_1(A_415,B_416,C_417) = k2_relat_1(C_417)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5466,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_5454])).

tff(c_5474,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5200,c_74,c_5466])).

tff(c_3297,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3194,c_3282])).

tff(c_3314,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k1_xboole_0
    | k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3297,c_24])).

tff(c_5314,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5121,c_5121,c_3314])).

tff(c_5315,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5314])).

tff(c_5318,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_5315])).

tff(c_5321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_82,c_76,c_5200,c_5318])).

tff(c_5322,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5314])).

tff(c_5326,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5322,c_3193])).

tff(c_5479,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5474,c_5326])).

tff(c_5959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5956,c_5479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:46:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.26  
% 6.32/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.27  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.32/2.27  
% 6.32/2.27  %Foreground sorts:
% 6.32/2.27  
% 6.32/2.27  
% 6.32/2.27  %Background operators:
% 6.32/2.27  
% 6.32/2.27  
% 6.32/2.27  %Foreground operators:
% 6.32/2.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.32/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.32/2.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.32/2.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.32/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.32/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.32/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.32/2.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.32/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.32/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.32/2.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.32/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.32/2.27  tff('#skF_1', type, '#skF_1': $i).
% 6.32/2.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.32/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.32/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.32/2.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.32/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.32/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.32/2.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.32/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.32/2.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.32/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.32/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.32/2.27  
% 6.32/2.30  tff(f_167, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.32/2.30  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.32/2.30  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.32/2.30  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.32/2.30  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.32/2.30  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.32/2.30  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.32/2.30  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.32/2.30  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 6.32/2.30  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 6.32/2.30  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 6.32/2.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.32/2.30  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 6.32/2.30  tff(f_150, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.32/2.30  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.32/2.30  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.32/2.30  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.32/2.30  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.32/2.30  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.32/2.30  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.32/2.30  tff(c_3282, plain, (![C_269, A_270, B_271]: (v1_relat_1(C_269) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.32/2.30  tff(c_3298, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3282])).
% 6.32/2.30  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.32/2.30  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.32/2.30  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.32/2.30  tff(c_3576, plain, (![A_302, B_303, C_304]: (k2_relset_1(A_302, B_303, C_304)=k2_relat_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.32/2.30  tff(c_3588, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3576])).
% 6.32/2.30  tff(c_3604, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3588])).
% 6.32/2.30  tff(c_46, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.32/2.30  tff(c_197, plain, (![A_46]: (v1_funct_1(k2_funct_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.32/2.30  tff(c_72, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.32/2.30  tff(c_183, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_72])).
% 6.32/2.30  tff(c_200, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_197, c_183])).
% 6.32/2.30  tff(c_203, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_200])).
% 6.32/2.30  tff(c_300, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.32/2.30  tff(c_303, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_300])).
% 6.32/2.30  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_203, c_303])).
% 6.32/2.30  tff(c_316, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_72])).
% 6.32/2.30  tff(c_391, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_316])).
% 6.32/2.30  tff(c_480, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.32/2.30  tff(c_492, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_480])).
% 6.32/2.30  tff(c_32, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.32/2.30  tff(c_684, plain, (![A_98, B_99, C_100]: (k2_relset_1(A_98, B_99, C_100)=k2_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.32/2.30  tff(c_693, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_684])).
% 6.32/2.30  tff(c_708, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_693])).
% 6.32/2.30  tff(c_22, plain, (![A_9]: (k2_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.32/2.30  tff(c_501, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_492, c_22])).
% 6.32/2.30  tff(c_518, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_501])).
% 6.32/2.30  tff(c_710, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_708, c_518])).
% 6.32/2.30  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.32/2.30  tff(c_627, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.32/2.30  tff(c_645, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_627])).
% 6.32/2.30  tff(c_1300, plain, (![B_143, A_144, C_145]: (k1_xboole_0=B_143 | k1_relset_1(A_144, B_143, C_145)=A_144 | ~v1_funct_2(C_145, A_144, B_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.32/2.30  tff(c_1315, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_1300])).
% 6.32/2.30  tff(c_1335, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_645, c_1315])).
% 6.32/2.30  tff(c_1336, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_710, c_1335])).
% 6.32/2.30  tff(c_541, plain, (![A_81]: (k2_relat_1(k2_funct_1(A_81))=k1_relat_1(A_81) | ~v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.32/2.30  tff(c_20, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.32/2.30  tff(c_1565, plain, (![A_160]: (k10_relat_1(k2_funct_1(A_160), k1_relat_1(A_160))=k1_relat_1(k2_funct_1(A_160)) | ~v1_relat_1(k2_funct_1(A_160)) | ~v2_funct_1(A_160) | ~v1_funct_1(A_160) | ~v1_relat_1(A_160))), inference(superposition, [status(thm), theory('equality')], [c_541, c_20])).
% 6.32/2.30  tff(c_1577, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1336, c_1565])).
% 6.32/2.30  tff(c_1591, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_82, c_76, c_1577])).
% 6.32/2.30  tff(c_1599, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1591])).
% 6.32/2.30  tff(c_1602, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1599])).
% 6.32/2.30  tff(c_1606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_492, c_82, c_1602])).
% 6.32/2.30  tff(c_1608, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1591])).
% 6.32/2.30  tff(c_317, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_72])).
% 6.32/2.30  tff(c_18, plain, (![A_7]: (k9_relat_1(A_7, k1_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.32/2.30  tff(c_1367, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1336, c_18])).
% 6.32/2.30  tff(c_1379, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_492, c_708, c_1367])).
% 6.32/2.30  tff(c_1607, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1591])).
% 6.32/2.30  tff(c_40, plain, (![B_16, A_15]: (k10_relat_1(k2_funct_1(B_16), A_15)=k9_relat_1(B_16, A_15) | ~v2_funct_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.32/2.30  tff(c_1620, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1607, c_40])).
% 6.32/2.30  tff(c_1627, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_492, c_82, c_76, c_1379, c_1620])).
% 6.32/2.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.32/2.30  tff(c_42, plain, (![A_17, B_19]: (k9_relat_1(k2_funct_1(A_17), k9_relat_1(A_17, B_19))=B_19 | ~r1_tarski(B_19, k1_relat_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.32/2.30  tff(c_1397, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1379, c_42])).
% 6.32/2.30  tff(c_1401, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_492, c_82, c_76, c_6, c_1336, c_1397])).
% 6.32/2.30  tff(c_1656, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1627, c_18])).
% 6.32/2.30  tff(c_1677, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1608, c_1401, c_1656])).
% 6.32/2.30  tff(c_66, plain, (![A_33]: (m1_subset_1(A_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33), k2_relat_1(A_33)))) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.32/2.30  tff(c_1699, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1677, c_66])).
% 6.32/2.30  tff(c_1728, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1608, c_317, c_1627, c_1699])).
% 6.32/2.30  tff(c_1730, plain, $false, inference(negUnitSimplification, [status(thm)], [c_391, c_1728])).
% 6.32/2.30  tff(c_1731, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_501])).
% 6.32/2.30  tff(c_28, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.32/2.30  tff(c_34, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.32/2.30  tff(c_149, plain, (![A_44]: (k2_relat_1(A_44)!=k1_xboole_0 | k1_xboole_0=A_44 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.32/2.30  tff(c_152, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))!=k1_xboole_0 | k6_relat_1(A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_149])).
% 6.32/2.30  tff(c_156, plain, (![A_45]: (k1_xboole_0!=A_45 | k6_relat_1(A_45)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_152])).
% 6.32/2.30  tff(c_26, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.32/2.30  tff(c_165, plain, (![A_45]: (k1_relat_1(k1_xboole_0)=A_45 | k1_xboole_0!=A_45)), inference(superposition, [status(thm), theory('equality')], [c_156, c_26])).
% 6.32/2.30  tff(c_1841, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1731, c_1731, c_165])).
% 6.32/2.30  tff(c_24, plain, (![A_9]: (k1_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.32/2.30  tff(c_500, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_492, c_24])).
% 6.32/2.30  tff(c_502, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_500])).
% 6.32/2.30  tff(c_1733, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1731, c_502])).
% 6.32/2.30  tff(c_1845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1841, c_1733])).
% 6.32/2.30  tff(c_1846, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_500])).
% 6.32/2.30  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.32/2.30  tff(c_1860, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1846, c_1846, c_12])).
% 6.32/2.30  tff(c_162, plain, (![A_45]: (k2_relat_1(k1_xboole_0)=A_45 | k1_xboole_0!=A_45)), inference(superposition, [status(thm), theory('equality')], [c_156, c_28])).
% 6.32/2.30  tff(c_1957, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1846, c_1846, c_162])).
% 6.32/2.30  tff(c_2152, plain, (![A_186, B_187, C_188]: (k2_relset_1(A_186, B_187, C_188)=k2_relat_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.32/2.30  tff(c_2164, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2152])).
% 6.32/2.30  tff(c_2171, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1957, c_74, c_2164])).
% 6.32/2.30  tff(c_2174, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2171, c_391])).
% 6.32/2.30  tff(c_2178, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1860, c_2174])).
% 6.32/2.30  tff(c_154, plain, (![A_12]: (k1_xboole_0!=A_12 | k6_relat_1(A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_152])).
% 6.32/2.30  tff(c_1856, plain, (![A_12]: (A_12!='#skF_3' | k6_relat_1(A_12)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1846, c_1846, c_154])).
% 6.32/2.30  tff(c_36, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.32/2.30  tff(c_425, plain, (![A_68]: (k9_relat_1(A_68, k1_relat_1(A_68))=k2_relat_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.32/2.30  tff(c_434, plain, (![A_10]: (k9_relat_1(k6_relat_1(A_10), A_10)=k2_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_425])).
% 6.32/2.30  tff(c_438, plain, (![A_10]: (k9_relat_1(k6_relat_1(A_10), A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_434])).
% 6.32/2.30  tff(c_2764, plain, (![A_244, B_245]: (k9_relat_1(k2_funct_1(A_244), k9_relat_1(A_244, B_245))=B_245 | ~r1_tarski(B_245, k1_relat_1(A_244)) | ~v2_funct_1(A_244) | ~v1_funct_1(A_244) | ~v1_relat_1(A_244))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.32/2.30  tff(c_2782, plain, (![A_10]: (k9_relat_1(k2_funct_1(k6_relat_1(A_10)), A_10)=A_10 | ~r1_tarski(A_10, k1_relat_1(k6_relat_1(A_10))) | ~v2_funct_1(k6_relat_1(A_10)) | ~v1_funct_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_438, c_2764])).
% 6.32/2.30  tff(c_2794, plain, (![A_246]: (k9_relat_1(k2_funct_1(k6_relat_1(A_246)), A_246)=A_246 | ~v1_funct_1(k6_relat_1(A_246)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_6, c_26, c_2782])).
% 6.32/2.30  tff(c_2845, plain, (![A_248]: (k9_relat_1(k2_funct_1('#skF_3'), A_248)=A_248 | ~v1_funct_1(k6_relat_1(A_248)) | A_248!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1856, c_2794])).
% 6.32/2.30  tff(c_2848, plain, (![A_12]: (k9_relat_1(k2_funct_1('#skF_3'), A_12)=A_12 | ~v1_funct_1('#skF_3') | A_12!='#skF_3' | A_12!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1856, c_2845])).
% 6.32/2.30  tff(c_2852, plain, (![A_249]: (k9_relat_1(k2_funct_1('#skF_3'), A_249)=A_249 | A_249!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2848])).
% 6.32/2.30  tff(c_2877, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2852])).
% 6.32/2.30  tff(c_3082, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2877])).
% 6.32/2.30  tff(c_3128, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_3082])).
% 6.32/2.30  tff(c_3132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_492, c_82, c_3128])).
% 6.32/2.30  tff(c_3134, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2877])).
% 6.32/2.30  tff(c_2866, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2852, c_18])).
% 6.32/2.30  tff(c_3145, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3134, c_2866])).
% 6.32/2.30  tff(c_3146, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_3145])).
% 6.32/2.30  tff(c_3149, plain, (k2_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_3146])).
% 6.32/2.30  tff(c_3152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_492, c_82, c_76, c_1957, c_3149])).
% 6.32/2.30  tff(c_3154, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_3145])).
% 6.32/2.30  tff(c_3167, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3154, c_66])).
% 6.32/2.30  tff(c_3190, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3134, c_317, c_1860, c_3167])).
% 6.32/2.30  tff(c_3192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2178, c_3190])).
% 6.32/2.30  tff(c_3193, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_316])).
% 6.32/2.30  tff(c_3194, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_316])).
% 6.32/2.30  tff(c_3428, plain, (![A_285, B_286, C_287]: (k1_relset_1(A_285, B_286, C_287)=k1_relat_1(C_287) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.32/2.30  tff(c_3445, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3194, c_3428])).
% 6.32/2.30  tff(c_3893, plain, (![B_329, C_330, A_331]: (k1_xboole_0=B_329 | v1_funct_2(C_330, A_331, B_329) | k1_relset_1(A_331, B_329, C_330)!=A_331 | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_331, B_329))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.32/2.30  tff(c_3908, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_3194, c_3893])).
% 6.32/2.30  tff(c_3930, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3445, c_3908])).
% 6.32/2.30  tff(c_3931, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3193, c_3930])).
% 6.32/2.30  tff(c_3953, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_3931])).
% 6.32/2.30  tff(c_3956, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_3953])).
% 6.32/2.30  tff(c_3959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3298, c_82, c_76, c_3604, c_3956])).
% 6.32/2.30  tff(c_3960, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3931])).
% 6.32/2.30  tff(c_3306, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3298, c_24])).
% 6.32/2.30  tff(c_3331, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3306])).
% 6.32/2.30  tff(c_3988, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3960, c_3331])).
% 6.32/2.30  tff(c_4001, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3960, c_3960, c_12])).
% 6.32/2.30  tff(c_4112, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4001, c_78])).
% 6.32/2.30  tff(c_3444, plain, (![B_4, C_287]: (k1_relset_1(k1_xboole_0, B_4, C_287)=k1_relat_1(C_287) | ~m1_subset_1(C_287, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3428])).
% 6.32/2.30  tff(c_4612, plain, (![B_364, C_365]: (k1_relset_1('#skF_1', B_364, C_365)=k1_relat_1(C_365) | ~m1_subset_1(C_365, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3960, c_3960, c_3444])).
% 6.32/2.30  tff(c_4620, plain, (![B_364]: (k1_relset_1('#skF_1', B_364, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4112, c_4612])).
% 6.32/2.30  tff(c_62, plain, (![B_31, C_32]: (k1_relset_1(k1_xboole_0, B_31, C_32)=k1_xboole_0 | ~v1_funct_2(C_32, k1_xboole_0, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_31))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.32/2.30  tff(c_84, plain, (![B_31, C_32]: (k1_relset_1(k1_xboole_0, B_31, C_32)=k1_xboole_0 | ~v1_funct_2(C_32, k1_xboole_0, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_62])).
% 6.32/2.30  tff(c_5089, plain, (![B_396, C_397]: (k1_relset_1('#skF_1', B_396, C_397)='#skF_1' | ~v1_funct_2(C_397, '#skF_1', B_396) | ~m1_subset_1(C_397, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3960, c_3960, c_3960, c_3960, c_84])).
% 6.32/2.30  tff(c_5102, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_80, c_5089])).
% 6.32/2.30  tff(c_5118, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4112, c_4620, c_5102])).
% 6.32/2.30  tff(c_5120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3988, c_5118])).
% 6.32/2.30  tff(c_5121, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3306])).
% 6.32/2.30  tff(c_5122, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3306])).
% 6.32/2.30  tff(c_5142, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5121, c_5122])).
% 6.32/2.30  tff(c_5135, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5121, c_5121, c_12])).
% 6.32/2.30  tff(c_14, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.32/2.30  tff(c_16, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.32/2.30  tff(c_83, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 6.32/2.30  tff(c_5424, plain, (![A_412, B_413, C_414]: (k1_relset_1(A_412, B_413, C_414)=k1_relat_1(C_414) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.32/2.30  tff(c_5795, plain, (![A_443, B_444]: (k1_relset_1(A_443, B_444, k2_zfmisc_1(A_443, B_444))=k1_relat_1(k2_zfmisc_1(A_443, B_444)))), inference(resolution, [status(thm)], [c_83, c_5424])).
% 6.32/2.30  tff(c_5804, plain, (![B_4]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_4))=k1_relset_1('#skF_3', B_4, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5135, c_5795])).
% 6.32/2.30  tff(c_5810, plain, (![B_4]: (k1_relset_1('#skF_3', B_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5142, c_5135, c_5804])).
% 6.32/2.30  tff(c_58, plain, (![C_32, B_31]: (v1_funct_2(C_32, k1_xboole_0, B_31) | k1_relset_1(k1_xboole_0, B_31, C_32)!=k1_xboole_0 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_31))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.32/2.30  tff(c_85, plain, (![C_32, B_31]: (v1_funct_2(C_32, k1_xboole_0, B_31) | k1_relset_1(k1_xboole_0, B_31, C_32)!=k1_xboole_0 | ~m1_subset_1(C_32, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_58])).
% 6.32/2.30  tff(c_5950, plain, (![C_454, B_455]: (v1_funct_2(C_454, '#skF_3', B_455) | k1_relset_1('#skF_3', B_455, C_454)!='#skF_3' | ~m1_subset_1(C_454, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5121, c_5121, c_5121, c_5121, c_85])).
% 6.32/2.30  tff(c_5953, plain, (![B_455]: (v1_funct_2('#skF_3', '#skF_3', B_455) | k1_relset_1('#skF_3', B_455, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_83, c_5950])).
% 6.32/2.30  tff(c_5956, plain, (![B_455]: (v1_funct_2('#skF_3', '#skF_3', B_455))), inference(demodulation, [status(thm), theory('equality')], [c_5810, c_5953])).
% 6.32/2.30  tff(c_5200, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5121, c_5121, c_162])).
% 6.32/2.30  tff(c_5454, plain, (![A_415, B_416, C_417]: (k2_relset_1(A_415, B_416, C_417)=k2_relat_1(C_417) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.32/2.30  tff(c_5466, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_5454])).
% 6.32/2.30  tff(c_5474, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5200, c_74, c_5466])).
% 6.32/2.30  tff(c_3297, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3194, c_3282])).
% 6.32/2.30  tff(c_3314, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k1_xboole_0 | k2_funct_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3297, c_24])).
% 6.32/2.30  tff(c_5314, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5121, c_5121, c_3314])).
% 6.32/2.30  tff(c_5315, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_5314])).
% 6.32/2.30  tff(c_5318, plain, (k2_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_5315])).
% 6.32/2.30  tff(c_5321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3298, c_82, c_76, c_5200, c_5318])).
% 6.32/2.30  tff(c_5322, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_5314])).
% 6.32/2.30  tff(c_5326, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5322, c_3193])).
% 6.32/2.30  tff(c_5479, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5474, c_5326])).
% 6.32/2.30  tff(c_5959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5956, c_5479])).
% 6.32/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.30  
% 6.32/2.30  Inference rules
% 6.32/2.30  ----------------------
% 6.32/2.30  #Ref     : 8
% 6.32/2.30  #Sup     : 1257
% 6.32/2.30  #Fact    : 0
% 6.32/2.30  #Define  : 0
% 6.32/2.30  #Split   : 21
% 6.32/2.30  #Chain   : 0
% 6.32/2.30  #Close   : 0
% 6.32/2.30  
% 6.32/2.30  Ordering : KBO
% 6.32/2.30  
% 6.32/2.30  Simplification rules
% 6.32/2.30  ----------------------
% 6.32/2.30  #Subsume      : 171
% 6.32/2.30  #Demod        : 1600
% 6.32/2.30  #Tautology    : 763
% 6.32/2.30  #SimpNegUnit  : 27
% 6.32/2.30  #BackRed      : 128
% 6.32/2.30  
% 6.32/2.30  #Partial instantiations: 0
% 6.32/2.30  #Strategies tried      : 1
% 6.32/2.30  
% 6.32/2.30  Timing (in seconds)
% 6.32/2.30  ----------------------
% 6.52/2.30  Preprocessing        : 0.36
% 6.52/2.30  Parsing              : 0.20
% 6.52/2.30  CNF conversion       : 0.02
% 6.52/2.30  Main loop            : 1.10
% 6.52/2.30  Inferencing          : 0.40
% 6.52/2.30  Reduction            : 0.40
% 6.52/2.30  Demodulation         : 0.29
% 6.52/2.30  BG Simplification    : 0.04
% 6.52/2.30  Subsumption          : 0.17
% 6.52/2.30  Abstraction          : 0.05
% 6.52/2.30  MUC search           : 0.00
% 6.52/2.30  Cooper               : 0.00
% 6.52/2.30  Total                : 1.53
% 6.52/2.30  Index Insertion      : 0.00
% 6.52/2.30  Index Deletion       : 0.00
% 6.52/2.30  Index Matching       : 0.00
% 6.52/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
