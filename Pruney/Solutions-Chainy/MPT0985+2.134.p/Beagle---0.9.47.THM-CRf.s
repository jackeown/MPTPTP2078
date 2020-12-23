%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:48 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 984 expanded)
%              Number of leaves         :   38 ( 331 expanded)
%              Depth                    :   12
%              Number of atoms          :  322 (2778 expanded)
%              Number of equality atoms :  113 ( 808 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_115,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_123,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_115])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1170,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1176,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1170])).

tff(c_1183,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1176])).

tff(c_26,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_277,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_280,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_277])).

tff(c_286,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_280])).

tff(c_16,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_150,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_123,c_16])).

tff(c_152,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_289,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_152])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_255,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_263,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_255])).

tff(c_397,plain,(
    ! [B_77,A_78,C_79] :
      ( k1_xboole_0 = B_77
      | k1_relset_1(A_78,B_77,C_79) = A_78
      | ~ v1_funct_2(C_79,A_78,B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_403,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_397])).

tff(c_411,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_263,c_403])).

tff(c_412,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_411])).

tff(c_10,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_173,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k10_relat_1(B_39,A_40),k1_relat_1(B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_179,plain,(
    ! [A_8] :
      ( r1_tarski(k1_relat_1(A_8),k1_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_173])).

tff(c_429,plain,
    ( r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_179])).

tff(c_443,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_123,c_412,c_429])).

tff(c_24,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_217,plain,(
    ! [A_49] :
      ( k1_relat_1(k2_funct_1(A_49)) = k2_relat_1(A_49)
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k10_relat_1(B_7,A_6),k1_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_565,plain,(
    ! [A_96,A_97] :
      ( r1_tarski(k10_relat_1(k2_funct_1(A_96),A_97),k2_relat_1(A_96))
      | ~ v1_relat_1(k2_funct_1(A_96))
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_8])).

tff(c_568,plain,(
    ! [A_97] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_3'),A_97),'#skF_2')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_565])).

tff(c_580,plain,(
    ! [A_97] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_3'),A_97),'#skF_2')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_568])).

tff(c_583,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_580])).

tff(c_586,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_583])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_586])).

tff(c_592,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_580])).

tff(c_20,plain,(
    ! [A_10] :
      ( v1_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_126,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_137,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_126])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_137])).

tff(c_143,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_340,plain,(
    ! [B_70,A_71] :
      ( m1_subset_1(B_70,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_70),A_71)))
      | ~ r1_tarski(k2_relat_1(B_70),A_71)
      | ~ v1_funct_1(B_70)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_952,plain,(
    ! [A_115,A_116] :
      ( m1_subset_1(k2_funct_1(A_115),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_115),A_116)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_115)),A_116)
      | ~ v1_funct_1(k2_funct_1(A_115))
      | ~ v1_relat_1(k2_funct_1(A_115))
      | ~ v2_funct_1(A_115)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_340])).

tff(c_976,plain,(
    ! [A_116] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_116)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_116)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_952])).

tff(c_994,plain,(
    ! [A_117] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_117)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_592,c_143,c_976])).

tff(c_142,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_172,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_1027,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_994,c_172])).

tff(c_1032,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1027])).

tff(c_1035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_443,c_412,c_1032])).

tff(c_1036,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_1037,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_1140,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1151,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1037,c_1140])).

tff(c_1297,plain,(
    ! [B_156,C_157,A_158] :
      ( k1_xboole_0 = B_156
      | v1_funct_2(C_157,A_158,B_156)
      | k1_relset_1(A_158,B_156,C_157) != A_158
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1303,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1037,c_1297])).

tff(c_1313,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_1303])).

tff(c_1314,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1036,c_1313])).

tff(c_1320,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1314])).

tff(c_1323,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1320])).

tff(c_1326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_1183,c_1323])).

tff(c_1327,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_18,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_151,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_123,c_18])).

tff(c_171,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_1343,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1327,c_171])).

tff(c_1186,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_152])).

tff(c_1337,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1327,c_1186])).

tff(c_1152,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1140])).

tff(c_52,plain,(
    ! [B_23,A_22,C_24] :
      ( k1_xboole_0 = B_23
      | k1_relset_1(A_22,B_23,C_24) = A_22
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1362,plain,(
    ! [B_160,A_161,C_162] :
      ( B_160 = '#skF_1'
      | k1_relset_1(A_161,B_160,C_162) = A_161
      | ~ v1_funct_2(C_162,A_161,B_160)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1327,c_52])).

tff(c_1371,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1362])).

tff(c_1377,plain,
    ( '#skF_2' = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1152,c_1371])).

tff(c_1379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1343,c_1337,c_1377])).

tff(c_1380,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_1383,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_152])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1390,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1380,c_12])).

tff(c_1408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1383,c_1390])).

tff(c_1409,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1418,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_2])).

tff(c_1410,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_1437,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_1410])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1416,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_1409,c_14])).

tff(c_2063,plain,(
    ! [B_256,A_257] :
      ( v1_funct_2(B_256,k1_relat_1(B_256),A_257)
      | ~ r1_tarski(k2_relat_1(B_256),A_257)
      | ~ v1_funct_1(B_256)
      | ~ v1_relat_1(B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2069,plain,(
    ! [A_257] :
      ( v1_funct_2('#skF_3','#skF_3',A_257)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_257)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1416,c_2063])).

tff(c_2071,plain,(
    ! [A_257] : v1_funct_2('#skF_3','#skF_3',A_257) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_1418,c_1437,c_2069])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1414,plain,(
    ! [A_2] : m1_subset_1('#skF_3',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_4])).

tff(c_2042,plain,(
    ! [A_251,B_252,C_253] :
      ( k2_relset_1(A_251,B_252,C_253) = k2_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2046,plain,(
    ! [A_251,B_252] : k2_relset_1(A_251,B_252,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1414,c_2042])).

tff(c_2048,plain,(
    ! [A_251,B_252] : k2_relset_1(A_251,B_252,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_2046])).

tff(c_2049,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2048,c_62])).

tff(c_1883,plain,(
    ! [A_234] :
      ( k1_relat_1(k2_funct_1(A_234)) = k2_relat_1(A_234)
      | ~ v2_funct_1(A_234)
      | ~ v1_funct_1(A_234)
      | ~ v1_relat_1(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1547,plain,(
    ! [A_181] :
      ( k1_relat_1(k2_funct_1(A_181)) = k2_relat_1(A_181)
      | ~ v2_funct_1(A_181)
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1703,plain,(
    ! [A_214,A_215] :
      ( r1_tarski(k10_relat_1(k2_funct_1(A_214),A_215),k2_relat_1(A_214))
      | ~ v1_relat_1(k2_funct_1(A_214))
      | ~ v2_funct_1(A_214)
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1547,c_8])).

tff(c_1709,plain,(
    ! [A_215] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_3'),A_215),'#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1437,c_1703])).

tff(c_1715,plain,(
    ! [A_215] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_3'),A_215),'#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_1709])).

tff(c_1716,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1715])).

tff(c_1719,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_1716])).

tff(c_1723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_1719])).

tff(c_1725,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1715])).

tff(c_1411,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != '#skF_3'
      | A_9 = '#skF_3'
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_1409,c_16])).

tff(c_1732,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1725,c_1411])).

tff(c_1746,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1732])).

tff(c_1749,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1746])).

tff(c_1752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_1416,c_1749])).

tff(c_1753,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1732])).

tff(c_1589,plain,(
    ! [A_189,B_190,C_191] :
      ( k2_relset_1(A_189,B_190,C_191) = k2_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1593,plain,(
    ! [A_189,B_190] : k2_relset_1(A_189,B_190,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1414,c_1589])).

tff(c_1595,plain,(
    ! [A_189,B_190] : k2_relset_1(A_189,B_190,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1593])).

tff(c_1596,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1595,c_62])).

tff(c_1449,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_1604,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1596,c_1449])).

tff(c_1770,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1753,c_1604])).

tff(c_1777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1770])).

tff(c_1779,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_36,plain,(
    ! [C_15,A_13,B_14] :
      ( v1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1804,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1779,c_36])).

tff(c_1846,plain,(
    ! [A_226] :
      ( k1_relat_1(A_226) != '#skF_3'
      | A_226 = '#skF_3'
      | ~ v1_relat_1(A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_1409,c_18])).

tff(c_1856,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1804,c_1846])).

tff(c_1862,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1856])).

tff(c_1895,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1883,c_1862])).

tff(c_1905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_64,c_1437,c_1895])).

tff(c_1906,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1856])).

tff(c_1829,plain,(
    ! [A_225] :
      ( k2_relat_1(A_225) != '#skF_3'
      | A_225 = '#skF_3'
      | ~ v1_relat_1(A_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_1409,c_16])).

tff(c_1839,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1804,c_1829])).

tff(c_1845,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1839])).

tff(c_1908,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1906,c_1845])).

tff(c_1915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1908])).

tff(c_1916,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1839])).

tff(c_1778,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_1920,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1916,c_1778])).

tff(c_2057,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_1920])).

tff(c_2074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2071,c_2057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:24:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.76  
% 4.51/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.76  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.51/1.76  
% 4.51/1.76  %Foreground sorts:
% 4.51/1.76  
% 4.51/1.76  
% 4.51/1.76  %Background operators:
% 4.51/1.76  
% 4.51/1.76  
% 4.51/1.76  %Foreground operators:
% 4.51/1.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.51/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.51/1.76  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.51/1.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.51/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.51/1.76  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 4.51/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.51/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.51/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.51/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.76  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.51/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.51/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.51/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.51/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.76  
% 4.57/1.79  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.57/1.79  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.57/1.79  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.57/1.79  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.57/1.79  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.57/1.79  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.57/1.79  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.57/1.79  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.57/1.79  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 4.57/1.79  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.57/1.79  tff(f_122, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.57/1.79  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.57/1.79  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.57/1.79  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.57/1.79  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.57/1.79  tff(c_115, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.57/1.79  tff(c_123, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_115])).
% 4.57/1.79  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.57/1.79  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.57/1.79  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.57/1.79  tff(c_1170, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.57/1.79  tff(c_1176, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1170])).
% 4.57/1.79  tff(c_1183, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1176])).
% 4.57/1.79  tff(c_26, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.57/1.79  tff(c_277, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.57/1.79  tff(c_280, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_277])).
% 4.57/1.79  tff(c_286, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_280])).
% 4.57/1.79  tff(c_16, plain, (![A_9]: (k2_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.57/1.79  tff(c_150, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_123, c_16])).
% 4.57/1.79  tff(c_152, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_150])).
% 4.57/1.79  tff(c_289, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_152])).
% 4.57/1.79  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.57/1.79  tff(c_255, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.57/1.79  tff(c_263, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_255])).
% 4.57/1.79  tff(c_397, plain, (![B_77, A_78, C_79]: (k1_xboole_0=B_77 | k1_relset_1(A_78, B_77, C_79)=A_78 | ~v1_funct_2(C_79, A_78, B_77) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.57/1.79  tff(c_403, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_397])).
% 4.57/1.79  tff(c_411, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_263, c_403])).
% 4.57/1.79  tff(c_412, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_289, c_411])).
% 4.57/1.79  tff(c_10, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.57/1.79  tff(c_173, plain, (![B_39, A_40]: (r1_tarski(k10_relat_1(B_39, A_40), k1_relat_1(B_39)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.57/1.79  tff(c_179, plain, (![A_8]: (r1_tarski(k1_relat_1(A_8), k1_relat_1(A_8)) | ~v1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_173])).
% 4.57/1.79  tff(c_429, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_412, c_179])).
% 4.57/1.79  tff(c_443, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_123, c_412, c_429])).
% 4.57/1.79  tff(c_24, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.57/1.79  tff(c_22, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.57/1.79  tff(c_217, plain, (![A_49]: (k1_relat_1(k2_funct_1(A_49))=k2_relat_1(A_49) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.57/1.79  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k10_relat_1(B_7, A_6), k1_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.57/1.79  tff(c_565, plain, (![A_96, A_97]: (r1_tarski(k10_relat_1(k2_funct_1(A_96), A_97), k2_relat_1(A_96)) | ~v1_relat_1(k2_funct_1(A_96)) | ~v2_funct_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(superposition, [status(thm), theory('equality')], [c_217, c_8])).
% 4.57/1.79  tff(c_568, plain, (![A_97]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_3'), A_97), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_565])).
% 4.57/1.79  tff(c_580, plain, (![A_97]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_3'), A_97), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_568])).
% 4.57/1.79  tff(c_583, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_580])).
% 4.57/1.79  tff(c_586, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_583])).
% 4.57/1.79  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_586])).
% 4.57/1.79  tff(c_592, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_580])).
% 4.57/1.79  tff(c_20, plain, (![A_10]: (v1_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.57/1.79  tff(c_60, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.57/1.79  tff(c_126, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 4.57/1.79  tff(c_137, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_126])).
% 4.57/1.79  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_137])).
% 4.57/1.79  tff(c_143, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 4.57/1.79  tff(c_340, plain, (![B_70, A_71]: (m1_subset_1(B_70, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_70), A_71))) | ~r1_tarski(k2_relat_1(B_70), A_71) | ~v1_funct_1(B_70) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.57/1.79  tff(c_952, plain, (![A_115, A_116]: (m1_subset_1(k2_funct_1(A_115), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_115), A_116))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_115)), A_116) | ~v1_funct_1(k2_funct_1(A_115)) | ~v1_relat_1(k2_funct_1(A_115)) | ~v2_funct_1(A_115) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(superposition, [status(thm), theory('equality')], [c_26, c_340])).
% 4.57/1.79  tff(c_976, plain, (![A_116]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_116))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_116) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_952])).
% 4.57/1.79  tff(c_994, plain, (![A_117]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_117))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_117))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_592, c_143, c_976])).
% 4.57/1.79  tff(c_142, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_60])).
% 4.57/1.79  tff(c_172, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_142])).
% 4.57/1.79  tff(c_1027, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_994, c_172])).
% 4.57/1.79  tff(c_1032, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1027])).
% 4.57/1.79  tff(c_1035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_443, c_412, c_1032])).
% 4.57/1.79  tff(c_1036, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_142])).
% 4.57/1.79  tff(c_1037, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_142])).
% 4.57/1.79  tff(c_1140, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.57/1.79  tff(c_1151, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1037, c_1140])).
% 4.57/1.79  tff(c_1297, plain, (![B_156, C_157, A_158]: (k1_xboole_0=B_156 | v1_funct_2(C_157, A_158, B_156) | k1_relset_1(A_158, B_156, C_157)!=A_158 | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_156))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.57/1.79  tff(c_1303, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1037, c_1297])).
% 4.57/1.79  tff(c_1313, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_1303])).
% 4.57/1.79  tff(c_1314, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1036, c_1313])).
% 4.57/1.79  tff(c_1320, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_1314])).
% 4.57/1.79  tff(c_1323, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1320])).
% 4.57/1.79  tff(c_1326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_1183, c_1323])).
% 4.57/1.79  tff(c_1327, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1314])).
% 4.57/1.79  tff(c_18, plain, (![A_9]: (k1_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.57/1.79  tff(c_151, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_123, c_18])).
% 4.57/1.79  tff(c_171, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_151])).
% 4.57/1.79  tff(c_1343, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1327, c_171])).
% 4.57/1.79  tff(c_1186, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_152])).
% 4.57/1.79  tff(c_1337, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1327, c_1186])).
% 4.57/1.79  tff(c_1152, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1140])).
% 4.57/1.79  tff(c_52, plain, (![B_23, A_22, C_24]: (k1_xboole_0=B_23 | k1_relset_1(A_22, B_23, C_24)=A_22 | ~v1_funct_2(C_24, A_22, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.57/1.79  tff(c_1362, plain, (![B_160, A_161, C_162]: (B_160='#skF_1' | k1_relset_1(A_161, B_160, C_162)=A_161 | ~v1_funct_2(C_162, A_161, B_160) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(demodulation, [status(thm), theory('equality')], [c_1327, c_52])).
% 4.57/1.79  tff(c_1371, plain, ('#skF_2'='#skF_1' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1362])).
% 4.57/1.79  tff(c_1377, plain, ('#skF_2'='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1152, c_1371])).
% 4.57/1.79  tff(c_1379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1343, c_1337, c_1377])).
% 4.57/1.79  tff(c_1380, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_151])).
% 4.57/1.79  tff(c_1383, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_152])).
% 4.57/1.79  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.57/1.79  tff(c_1390, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1380, c_12])).
% 4.57/1.79  tff(c_1408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1383, c_1390])).
% 4.57/1.79  tff(c_1409, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_150])).
% 4.57/1.79  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.57/1.79  tff(c_1418, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_2])).
% 4.57/1.79  tff(c_1410, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_150])).
% 4.57/1.79  tff(c_1437, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_1410])).
% 4.57/1.79  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.57/1.79  tff(c_1416, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_1409, c_14])).
% 4.57/1.79  tff(c_2063, plain, (![B_256, A_257]: (v1_funct_2(B_256, k1_relat_1(B_256), A_257) | ~r1_tarski(k2_relat_1(B_256), A_257) | ~v1_funct_1(B_256) | ~v1_relat_1(B_256))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.57/1.79  tff(c_2069, plain, (![A_257]: (v1_funct_2('#skF_3', '#skF_3', A_257) | ~r1_tarski(k2_relat_1('#skF_3'), A_257) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1416, c_2063])).
% 4.57/1.79  tff(c_2071, plain, (![A_257]: (v1_funct_2('#skF_3', '#skF_3', A_257))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_1418, c_1437, c_2069])).
% 4.57/1.79  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.57/1.79  tff(c_1414, plain, (![A_2]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_4])).
% 4.57/1.79  tff(c_2042, plain, (![A_251, B_252, C_253]: (k2_relset_1(A_251, B_252, C_253)=k2_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.57/1.79  tff(c_2046, plain, (![A_251, B_252]: (k2_relset_1(A_251, B_252, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1414, c_2042])).
% 4.57/1.79  tff(c_2048, plain, (![A_251, B_252]: (k2_relset_1(A_251, B_252, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_2046])).
% 4.57/1.79  tff(c_2049, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2048, c_62])).
% 4.57/1.79  tff(c_1883, plain, (![A_234]: (k1_relat_1(k2_funct_1(A_234))=k2_relat_1(A_234) | ~v2_funct_1(A_234) | ~v1_funct_1(A_234) | ~v1_relat_1(A_234))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.57/1.79  tff(c_1547, plain, (![A_181]: (k1_relat_1(k2_funct_1(A_181))=k2_relat_1(A_181) | ~v2_funct_1(A_181) | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.57/1.79  tff(c_1703, plain, (![A_214, A_215]: (r1_tarski(k10_relat_1(k2_funct_1(A_214), A_215), k2_relat_1(A_214)) | ~v1_relat_1(k2_funct_1(A_214)) | ~v2_funct_1(A_214) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(superposition, [status(thm), theory('equality')], [c_1547, c_8])).
% 4.57/1.79  tff(c_1709, plain, (![A_215]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_3'), A_215), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1437, c_1703])).
% 4.57/1.79  tff(c_1715, plain, (![A_215]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_3'), A_215), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_1709])).
% 4.57/1.79  tff(c_1716, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1715])).
% 4.57/1.79  tff(c_1719, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_1716])).
% 4.57/1.79  tff(c_1723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_1719])).
% 4.57/1.79  tff(c_1725, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1715])).
% 4.57/1.79  tff(c_1411, plain, (![A_9]: (k2_relat_1(A_9)!='#skF_3' | A_9='#skF_3' | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_1409, c_16])).
% 4.57/1.79  tff(c_1732, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1725, c_1411])).
% 4.57/1.79  tff(c_1746, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_1732])).
% 4.57/1.79  tff(c_1749, plain, (k1_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1746])).
% 4.57/1.79  tff(c_1752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_1416, c_1749])).
% 4.57/1.79  tff(c_1753, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1732])).
% 4.57/1.79  tff(c_1589, plain, (![A_189, B_190, C_191]: (k2_relset_1(A_189, B_190, C_191)=k2_relat_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.57/1.79  tff(c_1593, plain, (![A_189, B_190]: (k2_relset_1(A_189, B_190, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1414, c_1589])).
% 4.57/1.79  tff(c_1595, plain, (![A_189, B_190]: (k2_relset_1(A_189, B_190, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1593])).
% 4.57/1.79  tff(c_1596, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1595, c_62])).
% 4.57/1.79  tff(c_1449, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_142])).
% 4.57/1.79  tff(c_1604, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1596, c_1449])).
% 4.57/1.79  tff(c_1770, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1753, c_1604])).
% 4.57/1.79  tff(c_1777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1414, c_1770])).
% 4.57/1.79  tff(c_1779, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_142])).
% 4.57/1.79  tff(c_36, plain, (![C_15, A_13, B_14]: (v1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.57/1.79  tff(c_1804, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1779, c_36])).
% 4.57/1.79  tff(c_1846, plain, (![A_226]: (k1_relat_1(A_226)!='#skF_3' | A_226='#skF_3' | ~v1_relat_1(A_226))), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_1409, c_18])).
% 4.57/1.79  tff(c_1856, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1804, c_1846])).
% 4.57/1.79  tff(c_1862, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_1856])).
% 4.57/1.79  tff(c_1895, plain, (k2_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1883, c_1862])).
% 4.57/1.79  tff(c_1905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_64, c_1437, c_1895])).
% 4.57/1.79  tff(c_1906, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1856])).
% 4.57/1.79  tff(c_1829, plain, (![A_225]: (k2_relat_1(A_225)!='#skF_3' | A_225='#skF_3' | ~v1_relat_1(A_225))), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_1409, c_16])).
% 4.57/1.79  tff(c_1839, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1804, c_1829])).
% 4.57/1.79  tff(c_1845, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_1839])).
% 4.57/1.79  tff(c_1908, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1906, c_1845])).
% 4.57/1.79  tff(c_1915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1908])).
% 4.57/1.79  tff(c_1916, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1839])).
% 4.57/1.79  tff(c_1778, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_142])).
% 4.57/1.79  tff(c_1920, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1916, c_1778])).
% 4.57/1.79  tff(c_2057, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2049, c_1920])).
% 4.57/1.79  tff(c_2074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2071, c_2057])).
% 4.57/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.79  
% 4.57/1.79  Inference rules
% 4.57/1.79  ----------------------
% 4.57/1.79  #Ref     : 0
% 4.57/1.79  #Sup     : 416
% 4.57/1.79  #Fact    : 0
% 4.57/1.79  #Define  : 0
% 4.57/1.79  #Split   : 18
% 4.57/1.79  #Chain   : 0
% 4.57/1.79  #Close   : 0
% 4.57/1.79  
% 4.57/1.79  Ordering : KBO
% 4.57/1.79  
% 4.57/1.79  Simplification rules
% 4.57/1.79  ----------------------
% 4.57/1.79  #Subsume      : 41
% 4.57/1.79  #Demod        : 628
% 4.57/1.79  #Tautology    : 212
% 4.57/1.79  #SimpNegUnit  : 10
% 4.57/1.79  #BackRed      : 79
% 4.57/1.79  
% 4.57/1.79  #Partial instantiations: 0
% 4.57/1.79  #Strategies tried      : 1
% 4.57/1.79  
% 4.57/1.79  Timing (in seconds)
% 4.57/1.79  ----------------------
% 4.57/1.79  Preprocessing        : 0.36
% 4.57/1.79  Parsing              : 0.20
% 4.57/1.79  CNF conversion       : 0.02
% 4.57/1.79  Main loop            : 0.62
% 4.57/1.79  Inferencing          : 0.22
% 4.57/1.79  Reduction            : 0.21
% 4.57/1.79  Demodulation         : 0.15
% 4.57/1.79  BG Simplification    : 0.03
% 4.57/1.79  Subsumption          : 0.11
% 4.57/1.79  Abstraction          : 0.03
% 4.57/1.79  MUC search           : 0.00
% 4.57/1.79  Cooper               : 0.00
% 4.57/1.79  Total                : 1.04
% 4.57/1.79  Index Insertion      : 0.00
% 4.57/1.79  Index Deletion       : 0.00
% 4.57/1.79  Index Matching       : 0.00
% 4.57/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
