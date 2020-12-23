%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:56 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :  190 (1692 expanded)
%              Number of leaves         :   35 ( 582 expanded)
%              Depth                    :   18
%              Number of atoms          :  372 (3535 expanded)
%              Number of equality atoms :   83 ( 665 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_62,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2385,plain,(
    ! [C_232,A_233,B_234] :
      ( m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ r1_tarski(k2_relat_1(C_232),B_234)
      | ~ r1_tarski(k1_relat_1(C_232),A_233)
      | ~ v1_relat_1(C_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_125,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_133,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_125])).

tff(c_143,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_458,plain,(
    ! [B_100,A_101,C_102] :
      ( r1_tarski(B_100,k3_subset_1(A_101,C_102))
      | ~ r1_xboole_0(B_100,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_13] :
      ( r1_tarski(k3_subset_1(A_13,k2_subset_1(A_13)),k2_subset_1(A_13))
      | ~ m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,(
    ! [A_13] : r1_tarski(k3_subset_1(A_13,k2_subset_1(A_13)),k2_subset_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_71,plain,(
    ! [A_13] : r1_tarski(k3_subset_1(A_13,A_13),A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_68])).

tff(c_132,plain,(
    ! [A_13] :
      ( k3_subset_1(A_13,A_13) = A_13
      | ~ r1_tarski(A_13,k3_subset_1(A_13,A_13)) ) ),
    inference(resolution,[status(thm)],[c_71,c_125])).

tff(c_480,plain,(
    ! [C_102] :
      ( k3_subset_1(C_102,C_102) = C_102
      | ~ r1_xboole_0(C_102,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(C_102)) ) ),
    inference(resolution,[status(thm)],[c_458,c_132])).

tff(c_515,plain,(
    ! [C_103] :
      ( k3_subset_1(C_103,C_103) = C_103
      | ~ r1_xboole_0(C_103,C_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_480])).

tff(c_525,plain,(
    k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_515])).

tff(c_60,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56])).

tff(c_144,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_376,plain,(
    ! [C_86,A_87,B_88] :
      ( m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ r1_tarski(k2_relat_1(C_86),B_88)
      | ~ r1_tarski(k1_relat_1(C_86),A_87)
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    ! [A_23,B_24,C_25] :
      ( k1_relset_1(A_23,B_24,C_25) = k1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_867,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ r1_tarski(k2_relat_1(C_130),B_129)
      | ~ r1_tarski(k1_relat_1(C_130),A_128)
      | ~ v1_relat_1(C_130) ) ),
    inference(resolution,[status(thm)],[c_376,c_40])).

tff(c_872,plain,(
    ! [A_128] :
      ( k1_relset_1(A_128,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_128)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_867])).

tff(c_885,plain,(
    ! [A_131] :
      ( k1_relset_1(A_131,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_872])).

tff(c_895,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_885])).

tff(c_42,plain,(
    ! [C_28,A_26,B_27] :
      ( m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ r1_tarski(k2_relat_1(C_28),B_27)
      | ~ r1_tarski(k1_relat_1(C_28),A_26)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_790,plain,(
    ! [B_121,C_122,A_123] :
      ( k1_xboole_0 = B_121
      | v1_funct_2(C_122,A_123,B_121)
      | k1_relset_1(A_123,B_121,C_122) != A_123
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1465,plain,(
    ! [B_162,C_163,A_164] :
      ( k1_xboole_0 = B_162
      | v1_funct_2(C_163,A_164,B_162)
      | k1_relset_1(A_164,B_162,C_163) != A_164
      | ~ r1_tarski(k2_relat_1(C_163),B_162)
      | ~ r1_tarski(k1_relat_1(C_163),A_164)
      | ~ v1_relat_1(C_163) ) ),
    inference(resolution,[status(thm)],[c_42,c_790])).

tff(c_1474,plain,(
    ! [A_164] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_164,'#skF_1')
      | k1_relset_1(A_164,'#skF_1','#skF_2') != A_164
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_164)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_1465])).

tff(c_1489,plain,(
    ! [A_164] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2('#skF_2',A_164,'#skF_1')
      | k1_relset_1(A_164,'#skF_1','#skF_2') != A_164
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1474])).

tff(c_1493,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1489])).

tff(c_32,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1067,plain,(
    ! [A_145,A_146,C_147,B_148] :
      ( r1_tarski(A_145,k3_subset_1(A_146,C_147))
      | ~ r1_tarski(A_145,B_148)
      | ~ r1_xboole_0(B_148,C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(A_146))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_146)) ) ),
    inference(resolution,[status(thm)],[c_458,c_10])).

tff(c_1165,plain,(
    ! [A_153,C_154] :
      ( r1_tarski(k2_relat_1('#skF_2'),k3_subset_1(A_153,C_154))
      | ~ r1_xboole_0('#skF_1',C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(A_153))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(A_153)) ) ),
    inference(resolution,[status(thm)],[c_58,c_1067])).

tff(c_1203,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_xboole_0)
    | ~ r1_xboole_0('#skF_1',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_1165])).

tff(c_1230,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_xboole_0)
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12,c_1203])).

tff(c_1231,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1230])).

tff(c_1495,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1493,c_1231])).

tff(c_1531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1495])).

tff(c_1634,plain,(
    ! [A_168] :
      ( v1_funct_2('#skF_2',A_168,'#skF_1')
      | k1_relset_1(A_168,'#skF_1','#skF_2') != A_168
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_168) ) ),
    inference(splitRight,[status(thm)],[c_1489])).

tff(c_1646,plain,
    ( v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_1634])).

tff(c_1651,plain,(
    v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_1646])).

tff(c_1653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_1651])).

tff(c_1654,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1230])).

tff(c_121,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | ~ r1_xboole_0(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_12,c_121])).

tff(c_156,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_163,plain,(
    ! [A_48,A_13] :
      ( r1_tarski(A_48,A_13)
      | ~ r1_tarski(A_48,k3_subset_1(A_13,A_13)) ) ),
    inference(resolution,[status(thm)],[c_71,c_156])).

tff(c_488,plain,(
    ! [B_100,C_102] :
      ( r1_tarski(B_100,C_102)
      | ~ r1_xboole_0(B_100,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(C_102))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(C_102)) ) ),
    inference(resolution,[status(thm)],[c_458,c_163])).

tff(c_629,plain,(
    ! [B_110,C_111] :
      ( r1_tarski(B_110,C_111)
      | ~ r1_xboole_0(B_110,C_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(C_111)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_488])).

tff(c_638,plain,(
    ! [A_19] :
      ( r1_tarski(k1_xboole_0,A_19)
      | ~ r1_xboole_0(k1_xboole_0,A_19) ) ),
    inference(resolution,[status(thm)],[c_32,c_629])).

tff(c_645,plain,(
    ! [A_112] : r1_tarski(k1_xboole_0,A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_638])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_694,plain,(
    ! [A_112] :
      ( k1_xboole_0 = A_112
      | ~ r1_tarski(A_112,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_645,c_4])).

tff(c_1678,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1654,c_694])).

tff(c_193,plain,(
    ! [A_59,A_60] :
      ( r1_tarski(A_59,A_60)
      | ~ r1_tarski(A_59,k3_subset_1(A_60,A_60)) ) ),
    inference(resolution,[status(thm)],[c_71,c_156])).

tff(c_218,plain,(
    ! [A_63] : r1_tarski(k3_subset_1(k3_subset_1(A_63,A_63),k3_subset_1(A_63,A_63)),A_63) ),
    inference(resolution,[status(thm)],[c_71,c_193])).

tff(c_164,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,'#skF_1')
      | ~ r1_tarski(A_48,k2_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_58,c_156])).

tff(c_237,plain,(
    r1_tarski(k3_subset_1(k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')),k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))),'#skF_1') ),
    inference(resolution,[status(thm)],[c_218,c_164])).

tff(c_306,plain,
    ( k3_subset_1(k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')),k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))) = '#skF_1'
    | ~ r1_tarski('#skF_1',k3_subset_1(k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')),k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_237,c_4])).

tff(c_526,plain,(
    ~ r1_tarski('#skF_1',k3_subset_1(k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')),k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_1692,plain,(
    ~ r1_tarski('#skF_1',k3_subset_1(k3_subset_1(k1_xboole_0,k1_xboole_0),k3_subset_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1678,c_1678,c_1678,c_1678,c_526])).

tff(c_1710,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_525,c_525,c_1692])).

tff(c_1655,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1230])).

tff(c_512,plain,(
    ! [B_100,C_102] :
      ( r1_tarski(B_100,C_102)
      | ~ r1_xboole_0(B_100,C_102)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(C_102)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_488])).

tff(c_1761,plain,
    ( r1_tarski('#skF_1',k1_xboole_0)
    | ~ r1_xboole_0('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1655,c_512])).

tff(c_1776,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1761])).

tff(c_1778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1710,c_1776])).

tff(c_1779,plain,(
    k3_subset_1(k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2')),k3_subset_1(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_202,plain,(
    ! [A_60] : r1_tarski(k3_subset_1(k3_subset_1(A_60,A_60),k3_subset_1(A_60,A_60)),A_60) ),
    inference(resolution,[status(thm)],[c_71,c_193])).

tff(c_1813,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1779,c_202])).

tff(c_1838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_1813])).

tff(c_1839,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2399,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2385,c_1839])).

tff(c_2413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8,c_58,c_2399])).

tff(c_2414,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_4977,plain,(
    ! [C_454,A_455,B_456] :
      ( m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_455,B_456)))
      | ~ r1_tarski(k2_relat_1(C_454),B_456)
      | ~ r1_tarski(k1_relat_1(C_454),A_455)
      | ~ v1_relat_1(C_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2643,plain,(
    ! [B_279,A_280,C_281] :
      ( r1_tarski(B_279,k3_subset_1(A_280,C_281))
      | ~ r1_xboole_0(B_279,C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(A_280))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(A_280)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2435,plain,(
    ! [A_237,C_238,B_239] :
      ( r1_tarski(A_237,C_238)
      | ~ r1_tarski(B_239,C_238)
      | ~ r1_tarski(A_237,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2440,plain,(
    ! [A_237,A_13] :
      ( r1_tarski(A_237,A_13)
      | ~ r1_tarski(A_237,k3_subset_1(A_13,A_13)) ) ),
    inference(resolution,[status(thm)],[c_71,c_2435])).

tff(c_2659,plain,(
    ! [B_279,C_281] :
      ( r1_tarski(B_279,C_281)
      | ~ r1_xboole_0(B_279,C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(C_281))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(C_281)) ) ),
    inference(resolution,[status(thm)],[c_2643,c_2440])).

tff(c_2769,plain,(
    ! [B_287,C_288] :
      ( r1_tarski(B_287,C_288)
      | ~ r1_xboole_0(B_287,C_288)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(C_288)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2659])).

tff(c_2778,plain,(
    ! [A_19] :
      ( r1_tarski(k1_xboole_0,A_19)
      | ~ r1_xboole_0(k1_xboole_0,A_19) ) ),
    inference(resolution,[status(thm)],[c_32,c_2769])).

tff(c_2784,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_2778])).

tff(c_16,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2594,plain,(
    ! [C_271,A_272,B_273] :
      ( m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273)))
      | ~ r1_tarski(k2_relat_1(C_271),B_273)
      | ~ r1_tarski(k1_relat_1(C_271),A_272)
      | ~ v1_relat_1(C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2908,plain,(
    ! [C_300,A_301] :
      ( m1_subset_1(C_300,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_300),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_300),A_301)
      | ~ v1_relat_1(C_300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2594])).

tff(c_2910,plain,(
    ! [A_301] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_301)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2414,c_2908])).

tff(c_2914,plain,(
    ! [A_301] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2910])).

tff(c_2917,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2914])).

tff(c_2946,plain,(
    ! [A_306,B_307,C_308] :
      ( k1_relset_1(A_306,B_307,C_308) = k1_relat_1(C_308)
      | ~ r1_tarski(k2_relat_1(C_308),B_307)
      | ~ r1_tarski(k1_relat_1(C_308),A_306)
      | ~ v1_relat_1(C_308) ) ),
    inference(resolution,[status(thm)],[c_2594,c_40])).

tff(c_2951,plain,(
    ! [A_306,B_307] :
      ( k1_relset_1(A_306,B_307,'#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski('#skF_1',B_307)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_306)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2414,c_2946])).

tff(c_2963,plain,(
    ! [A_309,B_310] :
      ( k1_relset_1(A_309,B_310,'#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski('#skF_1',B_310)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2951])).

tff(c_3015,plain,(
    ! [A_316] :
      ( k1_relset_1(A_316,'#skF_1','#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_316) ) ),
    inference(resolution,[status(thm)],[c_8,c_2963])).

tff(c_3025,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_3015])).

tff(c_2972,plain,(
    ! [B_311,C_312,A_313] :
      ( k1_xboole_0 = B_311
      | v1_funct_2(C_312,A_313,B_311)
      | k1_relset_1(A_313,B_311,C_312) != A_313
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_313,B_311))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4185,plain,(
    ! [B_374,C_375,A_376] :
      ( k1_xboole_0 = B_374
      | v1_funct_2(C_375,A_376,B_374)
      | k1_relset_1(A_376,B_374,C_375) != A_376
      | ~ r1_tarski(k2_relat_1(C_375),B_374)
      | ~ r1_tarski(k1_relat_1(C_375),A_376)
      | ~ v1_relat_1(C_375) ) ),
    inference(resolution,[status(thm)],[c_42,c_2972])).

tff(c_4190,plain,(
    ! [B_374,A_376] :
      ( k1_xboole_0 = B_374
      | v1_funct_2('#skF_2',A_376,B_374)
      | k1_relset_1(A_376,B_374,'#skF_2') != A_376
      | ~ r1_tarski('#skF_1',B_374)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_376)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2414,c_4185])).

tff(c_4237,plain,(
    ! [B_384,A_385] :
      ( k1_xboole_0 = B_384
      | v1_funct_2('#skF_2',A_385,B_384)
      | k1_relset_1(A_385,B_384,'#skF_2') != A_385
      | ~ r1_tarski('#skF_1',B_384)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4190])).

tff(c_4435,plain,(
    ! [B_396] :
      ( k1_xboole_0 = B_396
      | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),B_396)
      | k1_relset_1(k1_relat_1('#skF_2'),B_396,'#skF_2') != k1_relat_1('#skF_2')
      | ~ r1_tarski('#skF_1',B_396) ) ),
    inference(resolution,[status(thm)],[c_8,c_4237])).

tff(c_2434,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_4440,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4435,c_2434])).

tff(c_4446,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3025,c_4440])).

tff(c_2655,plain,(
    ! [C_281] :
      ( k3_subset_1(C_281,C_281) = C_281
      | ~ r1_xboole_0(C_281,C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(C_281)) ) ),
    inference(resolution,[status(thm)],[c_2643,c_132])).

tff(c_2676,plain,(
    ! [C_282] :
      ( k3_subset_1(C_282,C_282) = C_282
      | ~ r1_xboole_0(C_282,C_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2655])).

tff(c_2685,plain,(
    k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_2676])).

tff(c_30,plain,(
    ! [B_16,A_15,C_18] :
      ( r1_tarski(B_16,k3_subset_1(A_15,C_18))
      | ~ r1_xboole_0(B_16,C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3030,plain,(
    ! [A_317,A_318,C_319] :
      ( k1_relset_1(A_317,k3_subset_1(A_318,C_319),'#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_317)
      | ~ r1_xboole_0('#skF_1',C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(A_318))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(A_318)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2963])).

tff(c_3266,plain,(
    ! [A_338,C_339] :
      ( k1_relset_1(k1_relat_1('#skF_2'),k3_subset_1(A_338,C_339),'#skF_2') = k1_relat_1('#skF_2')
      | ~ r1_xboole_0('#skF_1',C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(A_338))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(A_338)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3030])).

tff(c_3275,plain,
    ( k1_relset_1(k1_relat_1('#skF_2'),k1_xboole_0,'#skF_2') = k1_relat_1('#skF_2')
    | ~ r1_xboole_0('#skF_1',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2685,c_3266])).

tff(c_3279,plain,
    ( k1_relset_1(k1_relat_1('#skF_2'),k1_xboole_0,'#skF_2') = k1_relat_1('#skF_2')
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_12,c_3275])).

tff(c_3382,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_3279])).

tff(c_4466,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4446,c_3382])).

tff(c_4501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4466])).

tff(c_4503,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_3279])).

tff(c_2673,plain,(
    ! [B_279,C_281] :
      ( r1_tarski(B_279,C_281)
      | ~ r1_xboole_0(B_279,C_281)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(C_281)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2659])).

tff(c_4508,plain,
    ( r1_tarski('#skF_1',k1_xboole_0)
    | ~ r1_xboole_0('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4503,c_2673])).

tff(c_4523,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4508])).

tff(c_4525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2917,c_4523])).

tff(c_4527,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2914])).

tff(c_4536,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_4527,c_4])).

tff(c_4542,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2784,c_4536])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2484,plain,(
    ! [A_253,B_254,C_255] :
      ( k1_relset_1(A_253,B_254,C_255) = k1_relat_1(C_255)
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2492,plain,(
    ! [A_253,B_254] : k1_relset_1(A_253,B_254,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_2484])).

tff(c_2501,plain,(
    ! [A_253,B_254] : k1_relset_1(A_253,B_254,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2492])).

tff(c_18,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2555,plain,(
    ! [C_266,B_267] :
      ( v1_funct_2(C_266,k1_xboole_0,B_267)
      | k1_relset_1(k1_xboole_0,B_267,C_266) != k1_xboole_0
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_48])).

tff(c_2558,plain,(
    ! [B_267] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_267)
      | k1_relset_1(k1_xboole_0,B_267,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_70,c_2555])).

tff(c_2564,plain,(
    ! [B_267] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_2558])).

tff(c_4556,plain,(
    ! [B_267] : v1_funct_2('#skF_1','#skF_1',B_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4542,c_4542,c_2564])).

tff(c_4571,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4542,c_4542,c_38])).

tff(c_4550,plain,(
    ! [A_19] : r1_tarski('#skF_1',A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4542,c_2784])).

tff(c_4569,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4542,c_12])).

tff(c_4526,plain,(
    ! [A_301] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_301)
      | m1_subset_1('#skF_2',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_2914])).

tff(c_4633,plain,(
    ! [A_301] :
      ( ~ r1_tarski(k1_relat_1('#skF_2'),A_301)
      | m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4542,c_4526])).

tff(c_4678,plain,(
    ! [A_407] : ~ r1_tarski(k1_relat_1('#skF_2'),A_407) ),
    inference(splitLeft,[status(thm)],[c_4633])).

tff(c_4688,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_4678])).

tff(c_4689,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4633])).

tff(c_4708,plain,
    ( r1_tarski('#skF_2','#skF_1')
    | ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_4689,c_2673])).

tff(c_4713,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4569,c_4708])).

tff(c_4718,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4713,c_4])).

tff(c_4722,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4550,c_4718])).

tff(c_4725,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4722,c_4722,c_2434])).

tff(c_4731,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4571,c_4725])).

tff(c_4785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4556,c_4731])).

tff(c_4786,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4988,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4977,c_4786])).

tff(c_5001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8,c_8,c_2414,c_4988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:34:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.06  
% 5.48/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.06  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.48/2.06  
% 5.48/2.06  %Foreground sorts:
% 5.48/2.06  
% 5.48/2.06  
% 5.48/2.06  %Background operators:
% 5.48/2.06  
% 5.48/2.06  
% 5.48/2.06  %Foreground operators:
% 5.48/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.48/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.48/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.48/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.48/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.48/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.48/2.06  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.48/2.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.48/2.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.48/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.48/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.48/2.06  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.48/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.48/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.48/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.48/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.48/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.48/2.06  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.48/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.48/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.48/2.06  
% 5.48/2.09  tff(f_122, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 5.48/2.09  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.48/2.09  tff(f_91, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.48/2.09  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.48/2.09  tff(f_51, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.48/2.09  tff(f_53, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.48/2.09  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 5.48/2.09  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 5.48/2.09  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.48/2.09  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.48/2.09  tff(f_70, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.48/2.09  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.48/2.09  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.48/2.09  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.48/2.09  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.48/2.09  tff(c_62, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.48/2.09  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.48/2.09  tff(c_58, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.48/2.09  tff(c_2385, plain, (![C_232, A_233, B_234]: (m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~r1_tarski(k2_relat_1(C_232), B_234) | ~r1_tarski(k1_relat_1(C_232), A_233) | ~v1_relat_1(C_232))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.48/2.09  tff(c_125, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.48/2.09  tff(c_133, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_125])).
% 5.48/2.09  tff(c_143, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_133])).
% 5.48/2.09  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.48/2.09  tff(c_20, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.48/2.09  tff(c_22, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.48/2.09  tff(c_70, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 5.48/2.09  tff(c_458, plain, (![B_100, A_101, C_102]: (r1_tarski(B_100, k3_subset_1(A_101, C_102)) | ~r1_xboole_0(B_100, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(A_101)) | ~m1_subset_1(B_100, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.48/2.09  tff(c_24, plain, (![A_13]: (r1_tarski(k3_subset_1(A_13, k2_subset_1(A_13)), k2_subset_1(A_13)) | ~m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.48/2.09  tff(c_68, plain, (![A_13]: (r1_tarski(k3_subset_1(A_13, k2_subset_1(A_13)), k2_subset_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 5.48/2.09  tff(c_71, plain, (![A_13]: (r1_tarski(k3_subset_1(A_13, A_13), A_13))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_68])).
% 5.48/2.09  tff(c_132, plain, (![A_13]: (k3_subset_1(A_13, A_13)=A_13 | ~r1_tarski(A_13, k3_subset_1(A_13, A_13)))), inference(resolution, [status(thm)], [c_71, c_125])).
% 5.48/2.09  tff(c_480, plain, (![C_102]: (k3_subset_1(C_102, C_102)=C_102 | ~r1_xboole_0(C_102, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(C_102)))), inference(resolution, [status(thm)], [c_458, c_132])).
% 5.48/2.09  tff(c_515, plain, (![C_103]: (k3_subset_1(C_103, C_103)=C_103 | ~r1_xboole_0(C_103, C_103))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_480])).
% 5.48/2.09  tff(c_525, plain, (k3_subset_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_515])).
% 5.48/2.09  tff(c_60, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.48/2.09  tff(c_56, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.48/2.09  tff(c_64, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56])).
% 5.48/2.09  tff(c_144, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 5.48/2.09  tff(c_376, plain, (![C_86, A_87, B_88]: (m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~r1_tarski(k2_relat_1(C_86), B_88) | ~r1_tarski(k1_relat_1(C_86), A_87) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.48/2.09  tff(c_40, plain, (![A_23, B_24, C_25]: (k1_relset_1(A_23, B_24, C_25)=k1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.48/2.09  tff(c_867, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~r1_tarski(k2_relat_1(C_130), B_129) | ~r1_tarski(k1_relat_1(C_130), A_128) | ~v1_relat_1(C_130))), inference(resolution, [status(thm)], [c_376, c_40])).
% 5.48/2.09  tff(c_872, plain, (![A_128]: (k1_relset_1(A_128, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_128) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_867])).
% 5.48/2.09  tff(c_885, plain, (![A_131]: (k1_relset_1(A_131, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_131))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_872])).
% 5.48/2.09  tff(c_895, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_885])).
% 5.48/2.09  tff(c_42, plain, (![C_28, A_26, B_27]: (m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~r1_tarski(k2_relat_1(C_28), B_27) | ~r1_tarski(k1_relat_1(C_28), A_26) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.48/2.09  tff(c_790, plain, (![B_121, C_122, A_123]: (k1_xboole_0=B_121 | v1_funct_2(C_122, A_123, B_121) | k1_relset_1(A_123, B_121, C_122)!=A_123 | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_121))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.48/2.09  tff(c_1465, plain, (![B_162, C_163, A_164]: (k1_xboole_0=B_162 | v1_funct_2(C_163, A_164, B_162) | k1_relset_1(A_164, B_162, C_163)!=A_164 | ~r1_tarski(k2_relat_1(C_163), B_162) | ~r1_tarski(k1_relat_1(C_163), A_164) | ~v1_relat_1(C_163))), inference(resolution, [status(thm)], [c_42, c_790])).
% 5.48/2.09  tff(c_1474, plain, (![A_164]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_164, '#skF_1') | k1_relset_1(A_164, '#skF_1', '#skF_2')!=A_164 | ~r1_tarski(k1_relat_1('#skF_2'), A_164) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_1465])).
% 5.48/2.09  tff(c_1489, plain, (![A_164]: (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', A_164, '#skF_1') | k1_relset_1(A_164, '#skF_1', '#skF_2')!=A_164 | ~r1_tarski(k1_relat_1('#skF_2'), A_164))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1474])).
% 5.48/2.09  tff(c_1493, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1489])).
% 5.48/2.09  tff(c_32, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.48/2.09  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.48/2.09  tff(c_1067, plain, (![A_145, A_146, C_147, B_148]: (r1_tarski(A_145, k3_subset_1(A_146, C_147)) | ~r1_tarski(A_145, B_148) | ~r1_xboole_0(B_148, C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(A_146)) | ~m1_subset_1(B_148, k1_zfmisc_1(A_146)))), inference(resolution, [status(thm)], [c_458, c_10])).
% 5.48/2.09  tff(c_1165, plain, (![A_153, C_154]: (r1_tarski(k2_relat_1('#skF_2'), k3_subset_1(A_153, C_154)) | ~r1_xboole_0('#skF_1', C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(A_153)) | ~m1_subset_1('#skF_1', k1_zfmisc_1(A_153)))), inference(resolution, [status(thm)], [c_58, c_1067])).
% 5.48/2.09  tff(c_1203, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_xboole_0) | ~r1_xboole_0('#skF_1', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_525, c_1165])).
% 5.48/2.09  tff(c_1230, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_xboole_0) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12, c_1203])).
% 5.48/2.09  tff(c_1231, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1230])).
% 5.48/2.09  tff(c_1495, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1493, c_1231])).
% 5.48/2.09  tff(c_1531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1495])).
% 5.48/2.09  tff(c_1634, plain, (![A_168]: (v1_funct_2('#skF_2', A_168, '#skF_1') | k1_relset_1(A_168, '#skF_1', '#skF_2')!=A_168 | ~r1_tarski(k1_relat_1('#skF_2'), A_168))), inference(splitRight, [status(thm)], [c_1489])).
% 5.48/2.09  tff(c_1646, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_1634])).
% 5.48/2.09  tff(c_1651, plain, (v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_895, c_1646])).
% 5.48/2.09  tff(c_1653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_1651])).
% 5.48/2.09  tff(c_1654, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1230])).
% 5.48/2.09  tff(c_121, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | ~r1_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.48/2.09  tff(c_124, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_12, c_121])).
% 5.48/2.09  tff(c_156, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.48/2.09  tff(c_163, plain, (![A_48, A_13]: (r1_tarski(A_48, A_13) | ~r1_tarski(A_48, k3_subset_1(A_13, A_13)))), inference(resolution, [status(thm)], [c_71, c_156])).
% 5.48/2.09  tff(c_488, plain, (![B_100, C_102]: (r1_tarski(B_100, C_102) | ~r1_xboole_0(B_100, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(C_102)) | ~m1_subset_1(B_100, k1_zfmisc_1(C_102)))), inference(resolution, [status(thm)], [c_458, c_163])).
% 5.48/2.09  tff(c_629, plain, (![B_110, C_111]: (r1_tarski(B_110, C_111) | ~r1_xboole_0(B_110, C_111) | ~m1_subset_1(B_110, k1_zfmisc_1(C_111)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_488])).
% 5.48/2.09  tff(c_638, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19) | ~r1_xboole_0(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_32, c_629])).
% 5.48/2.09  tff(c_645, plain, (![A_112]: (r1_tarski(k1_xboole_0, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_638])).
% 5.48/2.09  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.48/2.09  tff(c_694, plain, (![A_112]: (k1_xboole_0=A_112 | ~r1_tarski(A_112, k1_xboole_0))), inference(resolution, [status(thm)], [c_645, c_4])).
% 5.48/2.09  tff(c_1678, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1654, c_694])).
% 5.48/2.09  tff(c_193, plain, (![A_59, A_60]: (r1_tarski(A_59, A_60) | ~r1_tarski(A_59, k3_subset_1(A_60, A_60)))), inference(resolution, [status(thm)], [c_71, c_156])).
% 5.48/2.09  tff(c_218, plain, (![A_63]: (r1_tarski(k3_subset_1(k3_subset_1(A_63, A_63), k3_subset_1(A_63, A_63)), A_63))), inference(resolution, [status(thm)], [c_71, c_193])).
% 5.48/2.09  tff(c_164, plain, (![A_48]: (r1_tarski(A_48, '#skF_1') | ~r1_tarski(A_48, k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_58, c_156])).
% 5.48/2.09  tff(c_237, plain, (r1_tarski(k3_subset_1(k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')), k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2'))), '#skF_1')), inference(resolution, [status(thm)], [c_218, c_164])).
% 5.48/2.09  tff(c_306, plain, (k3_subset_1(k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')), k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')))='#skF_1' | ~r1_tarski('#skF_1', k3_subset_1(k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')), k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(resolution, [status(thm)], [c_237, c_4])).
% 5.48/2.09  tff(c_526, plain, (~r1_tarski('#skF_1', k3_subset_1(k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')), k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitLeft, [status(thm)], [c_306])).
% 5.48/2.09  tff(c_1692, plain, (~r1_tarski('#skF_1', k3_subset_1(k3_subset_1(k1_xboole_0, k1_xboole_0), k3_subset_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1678, c_1678, c_1678, c_1678, c_526])).
% 5.48/2.09  tff(c_1710, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_525, c_525, c_525, c_1692])).
% 5.48/2.09  tff(c_1655, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1230])).
% 5.48/2.09  tff(c_512, plain, (![B_100, C_102]: (r1_tarski(B_100, C_102) | ~r1_xboole_0(B_100, C_102) | ~m1_subset_1(B_100, k1_zfmisc_1(C_102)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_488])).
% 5.48/2.09  tff(c_1761, plain, (r1_tarski('#skF_1', k1_xboole_0) | ~r1_xboole_0('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_1655, c_512])).
% 5.48/2.09  tff(c_1776, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1761])).
% 5.48/2.09  tff(c_1778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1710, c_1776])).
% 5.48/2.09  tff(c_1779, plain, (k3_subset_1(k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')), k3_subset_1(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')))='#skF_1'), inference(splitRight, [status(thm)], [c_306])).
% 5.48/2.09  tff(c_202, plain, (![A_60]: (r1_tarski(k3_subset_1(k3_subset_1(A_60, A_60), k3_subset_1(A_60, A_60)), A_60))), inference(resolution, [status(thm)], [c_71, c_193])).
% 5.48/2.09  tff(c_1813, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1779, c_202])).
% 5.48/2.09  tff(c_1838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_1813])).
% 5.48/2.09  tff(c_1839, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_64])).
% 5.48/2.09  tff(c_2399, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2385, c_1839])).
% 5.48/2.09  tff(c_2413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_8, c_58, c_2399])).
% 5.48/2.09  tff(c_2414, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_133])).
% 5.48/2.09  tff(c_4977, plain, (![C_454, A_455, B_456]: (m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_455, B_456))) | ~r1_tarski(k2_relat_1(C_454), B_456) | ~r1_tarski(k1_relat_1(C_454), A_455) | ~v1_relat_1(C_454))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.48/2.09  tff(c_2643, plain, (![B_279, A_280, C_281]: (r1_tarski(B_279, k3_subset_1(A_280, C_281)) | ~r1_xboole_0(B_279, C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(A_280)) | ~m1_subset_1(B_279, k1_zfmisc_1(A_280)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.48/2.09  tff(c_2435, plain, (![A_237, C_238, B_239]: (r1_tarski(A_237, C_238) | ~r1_tarski(B_239, C_238) | ~r1_tarski(A_237, B_239))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.48/2.09  tff(c_2440, plain, (![A_237, A_13]: (r1_tarski(A_237, A_13) | ~r1_tarski(A_237, k3_subset_1(A_13, A_13)))), inference(resolution, [status(thm)], [c_71, c_2435])).
% 5.48/2.09  tff(c_2659, plain, (![B_279, C_281]: (r1_tarski(B_279, C_281) | ~r1_xboole_0(B_279, C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(C_281)) | ~m1_subset_1(B_279, k1_zfmisc_1(C_281)))), inference(resolution, [status(thm)], [c_2643, c_2440])).
% 5.48/2.09  tff(c_2769, plain, (![B_287, C_288]: (r1_tarski(B_287, C_288) | ~r1_xboole_0(B_287, C_288) | ~m1_subset_1(B_287, k1_zfmisc_1(C_288)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2659])).
% 5.48/2.09  tff(c_2778, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19) | ~r1_xboole_0(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_32, c_2769])).
% 5.48/2.09  tff(c_2784, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_2778])).
% 5.48/2.09  tff(c_16, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.48/2.09  tff(c_2594, plain, (![C_271, A_272, B_273]: (m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))) | ~r1_tarski(k2_relat_1(C_271), B_273) | ~r1_tarski(k1_relat_1(C_271), A_272) | ~v1_relat_1(C_271))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.48/2.09  tff(c_2908, plain, (![C_300, A_301]: (m1_subset_1(C_300, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_300), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_300), A_301) | ~v1_relat_1(C_300))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2594])).
% 5.48/2.09  tff(c_2910, plain, (![A_301]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_301) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2414, c_2908])).
% 5.48/2.09  tff(c_2914, plain, (![A_301]: (m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_2'), A_301))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2910])).
% 5.48/2.09  tff(c_2917, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2914])).
% 5.48/2.09  tff(c_2946, plain, (![A_306, B_307, C_308]: (k1_relset_1(A_306, B_307, C_308)=k1_relat_1(C_308) | ~r1_tarski(k2_relat_1(C_308), B_307) | ~r1_tarski(k1_relat_1(C_308), A_306) | ~v1_relat_1(C_308))), inference(resolution, [status(thm)], [c_2594, c_40])).
% 5.48/2.09  tff(c_2951, plain, (![A_306, B_307]: (k1_relset_1(A_306, B_307, '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski('#skF_1', B_307) | ~r1_tarski(k1_relat_1('#skF_2'), A_306) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2414, c_2946])).
% 5.48/2.09  tff(c_2963, plain, (![A_309, B_310]: (k1_relset_1(A_309, B_310, '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski('#skF_1', B_310) | ~r1_tarski(k1_relat_1('#skF_2'), A_309))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2951])).
% 5.48/2.09  tff(c_3015, plain, (![A_316]: (k1_relset_1(A_316, '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_316))), inference(resolution, [status(thm)], [c_8, c_2963])).
% 5.48/2.09  tff(c_3025, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_3015])).
% 5.48/2.09  tff(c_2972, plain, (![B_311, C_312, A_313]: (k1_xboole_0=B_311 | v1_funct_2(C_312, A_313, B_311) | k1_relset_1(A_313, B_311, C_312)!=A_313 | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_313, B_311))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.48/2.09  tff(c_4185, plain, (![B_374, C_375, A_376]: (k1_xboole_0=B_374 | v1_funct_2(C_375, A_376, B_374) | k1_relset_1(A_376, B_374, C_375)!=A_376 | ~r1_tarski(k2_relat_1(C_375), B_374) | ~r1_tarski(k1_relat_1(C_375), A_376) | ~v1_relat_1(C_375))), inference(resolution, [status(thm)], [c_42, c_2972])).
% 5.48/2.09  tff(c_4190, plain, (![B_374, A_376]: (k1_xboole_0=B_374 | v1_funct_2('#skF_2', A_376, B_374) | k1_relset_1(A_376, B_374, '#skF_2')!=A_376 | ~r1_tarski('#skF_1', B_374) | ~r1_tarski(k1_relat_1('#skF_2'), A_376) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2414, c_4185])).
% 5.48/2.09  tff(c_4237, plain, (![B_384, A_385]: (k1_xboole_0=B_384 | v1_funct_2('#skF_2', A_385, B_384) | k1_relset_1(A_385, B_384, '#skF_2')!=A_385 | ~r1_tarski('#skF_1', B_384) | ~r1_tarski(k1_relat_1('#skF_2'), A_385))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4190])).
% 5.48/2.09  tff(c_4435, plain, (![B_396]: (k1_xboole_0=B_396 | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), B_396) | k1_relset_1(k1_relat_1('#skF_2'), B_396, '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski('#skF_1', B_396))), inference(resolution, [status(thm)], [c_8, c_4237])).
% 5.48/2.09  tff(c_2434, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 5.48/2.09  tff(c_4440, plain, (k1_xboole_0='#skF_1' | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4435, c_2434])).
% 5.48/2.09  tff(c_4446, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3025, c_4440])).
% 5.48/2.09  tff(c_2655, plain, (![C_281]: (k3_subset_1(C_281, C_281)=C_281 | ~r1_xboole_0(C_281, C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(C_281)))), inference(resolution, [status(thm)], [c_2643, c_132])).
% 5.48/2.09  tff(c_2676, plain, (![C_282]: (k3_subset_1(C_282, C_282)=C_282 | ~r1_xboole_0(C_282, C_282))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2655])).
% 5.48/2.09  tff(c_2685, plain, (k3_subset_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_2676])).
% 5.48/2.09  tff(c_30, plain, (![B_16, A_15, C_18]: (r1_tarski(B_16, k3_subset_1(A_15, C_18)) | ~r1_xboole_0(B_16, C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.48/2.09  tff(c_3030, plain, (![A_317, A_318, C_319]: (k1_relset_1(A_317, k3_subset_1(A_318, C_319), '#skF_2')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_317) | ~r1_xboole_0('#skF_1', C_319) | ~m1_subset_1(C_319, k1_zfmisc_1(A_318)) | ~m1_subset_1('#skF_1', k1_zfmisc_1(A_318)))), inference(resolution, [status(thm)], [c_30, c_2963])).
% 5.48/2.09  tff(c_3266, plain, (![A_338, C_339]: (k1_relset_1(k1_relat_1('#skF_2'), k3_subset_1(A_338, C_339), '#skF_2')=k1_relat_1('#skF_2') | ~r1_xboole_0('#skF_1', C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(A_338)) | ~m1_subset_1('#skF_1', k1_zfmisc_1(A_338)))), inference(resolution, [status(thm)], [c_8, c_3030])).
% 5.48/2.09  tff(c_3275, plain, (k1_relset_1(k1_relat_1('#skF_2'), k1_xboole_0, '#skF_2')=k1_relat_1('#skF_2') | ~r1_xboole_0('#skF_1', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2685, c_3266])).
% 5.48/2.09  tff(c_3279, plain, (k1_relset_1(k1_relat_1('#skF_2'), k1_xboole_0, '#skF_2')=k1_relat_1('#skF_2') | ~m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_12, c_3275])).
% 5.48/2.09  tff(c_3382, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3279])).
% 5.48/2.09  tff(c_4466, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4446, c_3382])).
% 5.48/2.09  tff(c_4501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_4466])).
% 5.48/2.09  tff(c_4503, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_3279])).
% 5.48/2.09  tff(c_2673, plain, (![B_279, C_281]: (r1_tarski(B_279, C_281) | ~r1_xboole_0(B_279, C_281) | ~m1_subset_1(B_279, k1_zfmisc_1(C_281)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2659])).
% 5.48/2.09  tff(c_4508, plain, (r1_tarski('#skF_1', k1_xboole_0) | ~r1_xboole_0('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_4503, c_2673])).
% 5.48/2.09  tff(c_4523, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4508])).
% 5.48/2.09  tff(c_4525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2917, c_4523])).
% 5.48/2.09  tff(c_4527, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2914])).
% 5.48/2.09  tff(c_4536, plain, (k1_xboole_0='#skF_1' | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_4527, c_4])).
% 5.48/2.09  tff(c_4542, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2784, c_4536])).
% 5.48/2.09  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.48/2.09  tff(c_2484, plain, (![A_253, B_254, C_255]: (k1_relset_1(A_253, B_254, C_255)=k1_relat_1(C_255) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.48/2.09  tff(c_2492, plain, (![A_253, B_254]: (k1_relset_1(A_253, B_254, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_2484])).
% 5.48/2.09  tff(c_2501, plain, (![A_253, B_254]: (k1_relset_1(A_253, B_254, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2492])).
% 5.48/2.09  tff(c_18, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.48/2.09  tff(c_48, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.48/2.09  tff(c_2555, plain, (![C_266, B_267]: (v1_funct_2(C_266, k1_xboole_0, B_267) | k1_relset_1(k1_xboole_0, B_267, C_266)!=k1_xboole_0 | ~m1_subset_1(C_266, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_48])).
% 5.48/2.09  tff(c_2558, plain, (![B_267]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_267) | k1_relset_1(k1_xboole_0, B_267, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_2555])).
% 5.48/2.09  tff(c_2564, plain, (![B_267]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_267))), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_2558])).
% 5.48/2.09  tff(c_4556, plain, (![B_267]: (v1_funct_2('#skF_1', '#skF_1', B_267))), inference(demodulation, [status(thm), theory('equality')], [c_4542, c_4542, c_2564])).
% 5.48/2.09  tff(c_4571, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4542, c_4542, c_38])).
% 5.48/2.09  tff(c_4550, plain, (![A_19]: (r1_tarski('#skF_1', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_4542, c_2784])).
% 5.48/2.09  tff(c_4569, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4542, c_12])).
% 5.48/2.09  tff(c_4526, plain, (![A_301]: (~r1_tarski(k1_relat_1('#skF_2'), A_301) | m1_subset_1('#skF_2', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_2914])).
% 5.48/2.09  tff(c_4633, plain, (![A_301]: (~r1_tarski(k1_relat_1('#skF_2'), A_301) | m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4542, c_4526])).
% 5.48/2.09  tff(c_4678, plain, (![A_407]: (~r1_tarski(k1_relat_1('#skF_2'), A_407))), inference(splitLeft, [status(thm)], [c_4633])).
% 5.48/2.09  tff(c_4688, plain, $false, inference(resolution, [status(thm)], [c_8, c_4678])).
% 5.48/2.09  tff(c_4689, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4633])).
% 5.48/2.09  tff(c_4708, plain, (r1_tarski('#skF_2', '#skF_1') | ~r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_4689, c_2673])).
% 5.48/2.09  tff(c_4713, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4569, c_4708])).
% 5.48/2.09  tff(c_4718, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4713, c_4])).
% 5.48/2.09  tff(c_4722, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4550, c_4718])).
% 5.48/2.09  tff(c_4725, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4722, c_4722, c_2434])).
% 5.48/2.09  tff(c_4731, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4571, c_4725])).
% 5.48/2.09  tff(c_4785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4556, c_4731])).
% 5.48/2.09  tff(c_4786, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_64])).
% 5.48/2.09  tff(c_4988, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4977, c_4786])).
% 5.48/2.09  tff(c_5001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_8, c_8, c_2414, c_4988])).
% 5.48/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.09  
% 5.48/2.09  Inference rules
% 5.48/2.09  ----------------------
% 5.48/2.09  #Ref     : 0
% 5.48/2.09  #Sup     : 994
% 5.48/2.09  #Fact    : 0
% 5.48/2.09  #Define  : 0
% 5.48/2.09  #Split   : 16
% 5.48/2.09  #Chain   : 0
% 5.48/2.09  #Close   : 0
% 5.48/2.09  
% 5.48/2.09  Ordering : KBO
% 5.48/2.09  
% 5.48/2.09  Simplification rules
% 5.48/2.09  ----------------------
% 5.48/2.09  #Subsume      : 120
% 5.48/2.09  #Demod        : 1140
% 5.48/2.09  #Tautology    : 404
% 5.48/2.09  #SimpNegUnit  : 4
% 5.48/2.09  #BackRed      : 141
% 5.48/2.09  
% 5.48/2.09  #Partial instantiations: 0
% 5.48/2.09  #Strategies tried      : 1
% 5.48/2.09  
% 5.48/2.09  Timing (in seconds)
% 5.48/2.09  ----------------------
% 5.48/2.09  Preprocessing        : 0.33
% 5.48/2.09  Parsing              : 0.18
% 5.48/2.09  CNF conversion       : 0.02
% 5.48/2.09  Main loop            : 0.92
% 5.48/2.09  Inferencing          : 0.31
% 5.48/2.09  Reduction            : 0.31
% 5.48/2.09  Demodulation         : 0.22
% 5.48/2.09  BG Simplification    : 0.04
% 5.48/2.09  Subsumption          : 0.19
% 5.48/2.09  Abstraction          : 0.05
% 5.48/2.09  MUC search           : 0.00
% 5.48/2.09  Cooper               : 0.00
% 5.48/2.09  Total                : 1.30
% 5.48/2.09  Index Insertion      : 0.00
% 5.48/2.09  Index Deletion       : 0.00
% 5.48/2.09  Index Matching       : 0.00
% 5.48/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
