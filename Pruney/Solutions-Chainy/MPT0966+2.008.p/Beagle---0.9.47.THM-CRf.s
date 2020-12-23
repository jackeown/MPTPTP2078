%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:08 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :  293 (3430 expanded)
%              Number of leaves         :   47 (1130 expanded)
%              Depth                    :   17
%              Number of atoms          :  476 (7728 expanded)
%              Number of equality atoms :  200 (3042 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4008,plain,(
    ! [A_495,B_496,C_497] :
      ( k2_relset_1(A_495,B_496,C_497) = k2_relat_1(C_497)
      | ~ m1_subset_1(C_497,k1_zfmisc_1(k2_zfmisc_1(A_495,B_496))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4027,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_4008])).

tff(c_68,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4029,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4027,c_68])).

tff(c_4151,plain,(
    ! [D_520,C_521,B_522,A_523] :
      ( m1_subset_1(D_520,k1_zfmisc_1(k2_zfmisc_1(C_521,B_522)))
      | ~ r1_tarski(k2_relat_1(D_520),B_522)
      | ~ m1_subset_1(D_520,k1_zfmisc_1(k2_zfmisc_1(C_521,A_523))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4246,plain,(
    ! [B_538] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_538)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_538) ) ),
    inference(resolution,[status(thm)],[c_70,c_4151])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_99,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_18,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_173,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_181,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_77,c_173])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_201,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_218,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_201])).

tff(c_36,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) = k1_xboole_0
      | k2_relat_1(A_23) != k1_xboole_0
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_230,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_218,c_36])).

tff(c_285,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_561,plain,(
    ! [A_126,B_127,C_128] :
      ( k2_relset_1(A_126,B_127,C_128) = k2_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_580,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_561])).

tff(c_582,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_68])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_76,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64])).

tff(c_245,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_687,plain,(
    ! [A_143,B_144,C_145] :
      ( k1_relset_1(A_143,B_144,C_145) = k1_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_706,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_687])).

tff(c_1040,plain,(
    ! [B_181,A_182,C_183] :
      ( k1_xboole_0 = B_181
      | k1_relset_1(A_182,B_181,C_183) = A_182
      | ~ v1_funct_2(C_183,A_182,B_181)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1050,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1040])).

tff(c_1065,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_706,c_1050])).

tff(c_1066,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_1065])).

tff(c_791,plain,(
    ! [D_160,C_161,B_162,A_163] :
      ( m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(C_161,B_162)))
      | ~ r1_tarski(k2_relat_1(D_160),B_162)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(C_161,A_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_833,plain,(
    ! [B_169] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_169)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_169) ) ),
    inference(resolution,[status(thm)],[c_70,c_791])).

tff(c_46,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_861,plain,(
    ! [B_169] :
      ( k1_relset_1('#skF_2',B_169,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_169) ) ),
    inference(resolution,[status(thm)],[c_833,c_46])).

tff(c_1168,plain,(
    ! [B_193] :
      ( k1_relset_1('#skF_2',B_193,'#skF_5') = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_861])).

tff(c_1180,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_582,c_1168])).

tff(c_805,plain,(
    ! [B_162] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_162)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_162) ) ),
    inference(resolution,[status(thm)],[c_70,c_791])).

tff(c_955,plain,(
    ! [B_174,C_175,A_176] :
      ( k1_xboole_0 = B_174
      | v1_funct_2(C_175,A_176,B_174)
      | k1_relset_1(A_176,B_174,C_175) != A_176
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1486,plain,(
    ! [B_227] :
      ( k1_xboole_0 = B_227
      | v1_funct_2('#skF_5','#skF_2',B_227)
      | k1_relset_1('#skF_2',B_227,'#skF_5') != '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_227) ) ),
    inference(resolution,[status(thm)],[c_805,c_955])).

tff(c_1489,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4')
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_582,c_1486])).

tff(c_1500,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_1489])).

tff(c_1501,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_1500])).

tff(c_859,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_833])).

tff(c_899,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_1525,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_899])).

tff(c_1565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_1525])).

tff(c_1566,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1596,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1566,c_22])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_231,plain,(
    ! [A_67,B_68] : v1_relat_1(k2_zfmisc_1(A_67,B_68)) ),
    inference(resolution,[status(thm)],[c_77,c_201])).

tff(c_236,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_231])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [A_48] :
      ( v1_xboole_0(k1_relat_1(A_48))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128,plain,(
    ! [A_49] :
      ( k1_relat_1(A_49) = k1_xboole_0
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_123,c_10])).

tff(c_136,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_266,plain,(
    ! [A_71] :
      ( k2_relat_1(A_71) = k1_xboole_0
      | k1_relat_1(A_71) != k1_xboole_0
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_269,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_236,c_266])).

tff(c_278,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_269])).

tff(c_303,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_324,plain,(
    ! [A_78,B_79] : v4_relat_1(k2_zfmisc_1(A_78,B_79),A_78) ),
    inference(resolution,[status(thm)],[c_77,c_303])).

tff(c_330,plain,(
    ! [A_7] : v4_relat_1(k1_xboole_0,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_324])).

tff(c_483,plain,(
    ! [B_116,A_117] :
      ( k7_relat_1(B_116,A_117) = B_116
      | ~ v4_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_492,plain,(
    ! [A_7] :
      ( k7_relat_1(k1_xboole_0,A_7) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_330,c_483])).

tff(c_520,plain,(
    ! [A_118] : k7_relat_1(k1_xboole_0,A_118) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_492])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(k7_relat_1(B_18,A_17)) = k9_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_525,plain,(
    ! [A_118] :
      ( k9_relat_1(k1_xboole_0,A_118) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_30])).

tff(c_530,plain,(
    ! [A_118] : k9_relat_1(k1_xboole_0,A_118) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_278,c_525])).

tff(c_636,plain,(
    ! [B_136,A_137] :
      ( k9_relat_1(B_136,A_137) != k1_xboole_0
      | ~ r1_tarski(A_137,k1_relat_1(B_136))
      | k1_xboole_0 = A_137
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_650,plain,(
    ! [A_137] :
      ( k9_relat_1(k1_xboole_0,A_137) != k1_xboole_0
      | ~ r1_tarski(A_137,k1_xboole_0)
      | k1_xboole_0 = A_137
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_636])).

tff(c_654,plain,(
    ! [A_137] :
      ( ~ r1_tarski(A_137,k1_xboole_0)
      | k1_xboole_0 = A_137 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_530,c_650])).

tff(c_1655,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1596,c_654])).

tff(c_1704,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1655,c_8])).

tff(c_1689,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1655,c_1655,c_278])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_331,plain,(
    ! [C_80,B_81,A_82] :
      ( ~ v1_xboole_0(C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_343,plain,(
    ! [A_84,A_85] :
      ( ~ v1_xboole_0(A_84)
      | ~ r2_hidden(A_85,A_84) ) ),
    inference(resolution,[status(thm)],[c_77,c_331])).

tff(c_347,plain,(
    ! [A_1,B_2] :
      ( ~ v1_xboole_0(A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_343])).

tff(c_42,plain,(
    ! [C_29,B_28,A_27] :
      ( v5_relat_1(C_29,B_28)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_870,plain,(
    ! [B_170] :
      ( v5_relat_1('#skF_5',B_170)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_170) ) ),
    inference(resolution,[status(thm)],[c_833,c_42])).

tff(c_883,plain,(
    ! [B_2] :
      ( v5_relat_1('#skF_5',B_2)
      | ~ v1_xboole_0(k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_347,c_870])).

tff(c_898,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_883])).

tff(c_1772,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1689,c_898])).

tff(c_1779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1704,c_1772])).

tff(c_1781,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_883])).

tff(c_1829,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1781,c_10])).

tff(c_1838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_1829])).

tff(c_1839,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_280,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_218,c_266])).

tff(c_1854,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1839,c_280])).

tff(c_2384,plain,(
    ! [D_323,C_324,B_325,A_326] :
      ( m1_subset_1(D_323,k1_zfmisc_1(k2_zfmisc_1(C_324,B_325)))
      | ~ r1_tarski(k2_relat_1(D_323),B_325)
      | ~ m1_subset_1(D_323,k1_zfmisc_1(k2_zfmisc_1(C_324,A_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2389,plain,(
    ! [B_325] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_325)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_325) ) ),
    inference(resolution,[status(thm)],[c_70,c_2384])).

tff(c_2424,plain,(
    ! [B_329] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_329)))
      | ~ r1_tarski(k1_xboole_0,B_329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_2389])).

tff(c_2450,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2424])).

tff(c_2465,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_2450])).

tff(c_2485,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2465,c_22])).

tff(c_1954,plain,(
    ! [C_260,A_261,B_262] :
      ( v4_relat_1(C_260,A_261)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1985,plain,(
    ! [A_263,B_264] : v4_relat_1(k2_zfmisc_1(A_263,B_264),A_263) ),
    inference(resolution,[status(thm)],[c_77,c_1954])).

tff(c_2026,plain,(
    ! [A_268] : v4_relat_1(k1_xboole_0,A_268) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1985])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2029,plain,(
    ! [A_268] :
      ( k7_relat_1(k1_xboole_0,A_268) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2026,c_34])).

tff(c_2032,plain,(
    ! [A_268] : k7_relat_1(k1_xboole_0,A_268) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_2029])).

tff(c_2058,plain,(
    ! [B_276,A_277] :
      ( k2_relat_1(k7_relat_1(B_276,A_277)) = k9_relat_1(B_276,A_277)
      | ~ v1_relat_1(B_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2067,plain,(
    ! [A_268] :
      ( k9_relat_1(k1_xboole_0,A_268) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2032,c_2058])).

tff(c_2074,plain,(
    ! [A_268] : k9_relat_1(k1_xboole_0,A_268) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_278,c_2067])).

tff(c_2200,plain,(
    ! [B_297,A_298] :
      ( k9_relat_1(B_297,A_298) != k1_xboole_0
      | ~ r1_tarski(A_298,k1_relat_1(B_297))
      | k1_xboole_0 = A_298
      | ~ v1_relat_1(B_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2217,plain,(
    ! [A_298] :
      ( k9_relat_1(k1_xboole_0,A_298) != k1_xboole_0
      | ~ r1_tarski(A_298,k1_xboole_0)
      | k1_xboole_0 = A_298
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_2200])).

tff(c_2223,plain,(
    ! [A_298] :
      ( ~ r1_tarski(A_298,k1_xboole_0)
      | k1_xboole_0 = A_298 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_2074,c_2217])).

tff(c_2523,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2485,c_2223])).

tff(c_2566,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_99])).

tff(c_2150,plain,(
    ! [A_288,B_289,C_290] :
      ( k1_relset_1(A_288,B_289,C_290) = k1_relat_1(C_290)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2157,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_2150])).

tff(c_2170,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1839,c_2157])).

tff(c_2541,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_2170])).

tff(c_62,plain,(
    ! [B_41,A_40,C_42] :
      ( k1_xboole_0 = B_41
      | k1_relset_1(A_40,B_41,C_42) = A_40
      | ~ v1_funct_2(C_42,A_40,B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2672,plain,(
    ! [B_340,A_341,C_342] :
      ( B_340 = '#skF_5'
      | k1_relset_1(A_341,B_340,C_342) = A_341
      | ~ v1_funct_2(C_342,A_341,B_340)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_341,B_340))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_62])).

tff(c_2679,plain,
    ( '#skF_5' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2672])).

tff(c_2687,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2541,c_2679])).

tff(c_2688,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2566,c_2687])).

tff(c_2568,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_8])).

tff(c_2701,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_2568])).

tff(c_2564,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_5',B_8) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_2523,c_16])).

tff(c_2809,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_2',B_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_2688,c_2564])).

tff(c_1876,plain,(
    ! [C_243,B_244,A_245] :
      ( ~ v1_xboole_0(C_243)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(C_243))
      | ~ r2_hidden(A_245,B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1884,plain,(
    ! [A_245] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_245,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_1876])).

tff(c_1935,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1884])).

tff(c_2810,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2809,c_1935])).

tff(c_2813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2701,c_2810])).

tff(c_2815,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1884])).

tff(c_2852,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2815,c_10])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2865,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2852,c_12])).

tff(c_2871,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_2865])).

tff(c_2885,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2871,c_2871,c_136])).

tff(c_2887,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_2',B_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2871,c_2871,c_16])).

tff(c_3183,plain,(
    ! [A_383,B_384,C_385] :
      ( k1_relset_1(A_383,B_384,C_385) = k1_relat_1(C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3641,plain,(
    ! [A_444,B_445] : k1_relset_1(A_444,B_445,k2_zfmisc_1(A_444,B_445)) = k1_relat_1(k2_zfmisc_1(A_444,B_445)) ),
    inference(resolution,[status(thm)],[c_77,c_3183])).

tff(c_3653,plain,(
    ! [B_8] : k1_relat_1(k2_zfmisc_1('#skF_2',B_8)) = k1_relset_1('#skF_2',B_8,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2887,c_3641])).

tff(c_3657,plain,(
    ! [B_8] : k1_relset_1('#skF_2',B_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2885,c_2887,c_3653])).

tff(c_56,plain,(
    ! [C_42,B_41] :
      ( v1_funct_2(C_42,k1_xboole_0,B_41)
      | k1_relset_1(k1_xboole_0,B_41,C_42) != k1_xboole_0
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_79,plain,(
    ! [C_42,B_41] :
      ( v1_funct_2(C_42,k1_xboole_0,B_41)
      | k1_relset_1(k1_xboole_0,B_41,C_42) != k1_xboole_0
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_56])).

tff(c_3457,plain,(
    ! [C_417,B_418] :
      ( v1_funct_2(C_417,'#skF_2',B_418)
      | k1_relset_1('#skF_2',B_418,C_417) != '#skF_2'
      | ~ m1_subset_1(C_417,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2871,c_2871,c_2871,c_2871,c_79])).

tff(c_3607,plain,(
    ! [B_441] :
      ( v1_funct_2('#skF_2','#skF_2',B_441)
      | k1_relset_1('#skF_2',B_441,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_77,c_3457])).

tff(c_2820,plain,(
    ! [A_354] : ~ r2_hidden(A_354,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1884])).

tff(c_2825,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_2820])).

tff(c_2880,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2871,c_236])).

tff(c_2876,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2871,c_2871,c_278])).

tff(c_2888,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2871,c_2871,c_14])).

tff(c_2913,plain,(
    ! [C_356,A_357,B_358] :
      ( v4_relat_1(C_356,A_357)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3010,plain,(
    ! [A_362,B_363] : v4_relat_1(k2_zfmisc_1(A_362,B_363),A_362) ),
    inference(resolution,[status(thm)],[c_77,c_2913])).

tff(c_3040,plain,(
    ! [A_367] : v4_relat_1('#skF_2',A_367) ),
    inference(superposition,[status(thm),theory(equality)],[c_2888,c_3010])).

tff(c_3043,plain,(
    ! [A_367] :
      ( k7_relat_1('#skF_2',A_367) = '#skF_2'
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3040,c_34])).

tff(c_3046,plain,(
    ! [A_367] : k7_relat_1('#skF_2',A_367) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2880,c_3043])).

tff(c_3093,plain,(
    ! [B_374,A_375] :
      ( k2_relat_1(k7_relat_1(B_374,A_375)) = k9_relat_1(B_374,A_375)
      | ~ v1_relat_1(B_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3102,plain,(
    ! [A_367] :
      ( k9_relat_1('#skF_2',A_367) = k2_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3046,c_3093])).

tff(c_3106,plain,(
    ! [A_367] : k9_relat_1('#skF_2',A_367) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2880,c_2876,c_3102])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( k9_relat_1(B_20,A_19) != k1_xboole_0
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3340,plain,(
    ! [B_412,A_413] :
      ( k9_relat_1(B_412,A_413) != '#skF_2'
      | ~ r1_tarski(A_413,k1_relat_1(B_412))
      | A_413 = '#skF_2'
      | ~ v1_relat_1(B_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2871,c_2871,c_32])).

tff(c_3346,plain,(
    ! [A_413] :
      ( k9_relat_1('#skF_2',A_413) != '#skF_2'
      | ~ r1_tarski(A_413,'#skF_2')
      | A_413 = '#skF_2'
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2885,c_3340])).

tff(c_3369,plain,(
    ! [A_414] :
      ( ~ r1_tarski(A_414,'#skF_2')
      | A_414 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2880,c_3106,c_3346])).

tff(c_3382,plain,(
    '#skF_5' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2825,c_3369])).

tff(c_3395,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3382,c_245])).

tff(c_3619,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3607,c_3395])).

tff(c_3690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3657,c_3619])).

tff(c_3691,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_4265,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4246,c_3691])).

tff(c_4286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4029,c_4265])).

tff(c_4288,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4287,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4295,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_4287])).

tff(c_4290,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4287,c_8])).

tff(c_4300,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4295,c_4290])).

tff(c_4339,plain,(
    ! [A_543] :
      ( v1_xboole_0(k1_relat_1(A_543))
      | ~ v1_xboole_0(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4289,plain,(
    ! [A_6] :
      ( A_6 = '#skF_2'
      | ~ v1_xboole_0(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4287,c_10])).

tff(c_4315,plain,(
    ! [A_6] :
      ( A_6 = '#skF_3'
      | ~ v1_xboole_0(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4295,c_4289])).

tff(c_4344,plain,(
    ! [A_544] :
      ( k1_relat_1(A_544) = '#skF_3'
      | ~ v1_xboole_0(A_544) ) ),
    inference(resolution,[status(thm)],[c_4339,c_4315])).

tff(c_4352,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4300,c_4344])).

tff(c_4322,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_3',B_8) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_4288,c_16])).

tff(c_5494,plain,(
    ! [A_707,B_708,C_709] :
      ( k1_relset_1(A_707,B_708,C_709) = k1_relat_1(C_709)
      | ~ m1_subset_1(C_709,k1_zfmisc_1(k2_zfmisc_1(A_707,B_708))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5649,plain,(
    ! [A_730,B_731] : k1_relset_1(A_730,B_731,k2_zfmisc_1(A_730,B_731)) = k1_relat_1(k2_zfmisc_1(A_730,B_731)) ),
    inference(resolution,[status(thm)],[c_77,c_5494])).

tff(c_5658,plain,(
    ! [B_8] : k1_relat_1(k2_zfmisc_1('#skF_3',B_8)) = k1_relset_1('#skF_3',B_8,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4322,c_5649])).

tff(c_5664,plain,(
    ! [B_8] : k1_relset_1('#skF_3',B_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4352,c_4322,c_5658])).

tff(c_5743,plain,(
    ! [C_743,B_744] :
      ( v1_funct_2(C_743,'#skF_3',B_744)
      | k1_relset_1('#skF_3',B_744,C_743) != '#skF_3'
      | ~ m1_subset_1(C_743,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_4288,c_4288,c_4288,c_79])).

tff(c_5749,plain,(
    ! [B_744] :
      ( v1_funct_2('#skF_3','#skF_3',B_744)
      | k1_relset_1('#skF_3',B_744,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_77,c_5743])).

tff(c_5753,plain,(
    ! [B_744] : v1_funct_2('#skF_3','#skF_3',B_744) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5664,c_5749])).

tff(c_4306,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_4288,c_14])).

tff(c_4362,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4306,c_4295,c_70])).

tff(c_4934,plain,(
    ! [C_628,B_629,A_630] :
      ( ~ v1_xboole_0(C_628)
      | ~ m1_subset_1(B_629,k1_zfmisc_1(C_628))
      | ~ r2_hidden(A_630,B_629) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4938,plain,(
    ! [A_630] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_630,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4362,c_4934])).

tff(c_4946,plain,(
    ! [A_631] : ~ r2_hidden(A_631,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4300,c_4938])).

tff(c_4951,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_4946])).

tff(c_4418,plain,(
    ! [C_557,A_558,B_559] :
      ( v1_relat_1(C_557)
      | ~ m1_subset_1(C_557,k1_zfmisc_1(k2_zfmisc_1(A_558,B_559))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4464,plain,(
    ! [C_563] :
      ( v1_relat_1(C_563)
      | ~ m1_subset_1(C_563,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4322,c_4418])).

tff(c_4477,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4362,c_4464])).

tff(c_4433,plain,(
    ! [A_560,B_561] : v1_relat_1(k2_zfmisc_1(A_560,B_561)) ),
    inference(resolution,[status(thm)],[c_77,c_4418])).

tff(c_4438,plain,(
    v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4322,c_4433])).

tff(c_38,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) = k1_xboole_0
      | k1_relat_1(A_23) != k1_xboole_0
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4449,plain,(
    ! [A_562] :
      ( k2_relat_1(A_562) = '#skF_3'
      | k1_relat_1(A_562) != '#skF_3'
      | ~ v1_relat_1(A_562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_4288,c_38])).

tff(c_4452,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | k1_relat_1('#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4438,c_4449])).

tff(c_4458,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4352,c_4452])).

tff(c_4700,plain,(
    ! [C_610,A_611,B_612] :
      ( v4_relat_1(C_610,A_611)
      | ~ m1_subset_1(C_610,k1_zfmisc_1(k2_zfmisc_1(A_611,B_612))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4731,plain,(
    ! [A_615,B_616] : v4_relat_1(k2_zfmisc_1(A_615,B_616),A_615) ),
    inference(resolution,[status(thm)],[c_77,c_4700])).

tff(c_4751,plain,(
    ! [A_617] : v4_relat_1('#skF_3',A_617) ),
    inference(superposition,[status(thm),theory(equality)],[c_4306,c_4731])).

tff(c_4754,plain,(
    ! [A_617] :
      ( k7_relat_1('#skF_3',A_617) = '#skF_3'
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4751,c_34])).

tff(c_4793,plain,(
    ! [A_620] : k7_relat_1('#skF_3',A_620) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4438,c_4754])).

tff(c_4798,plain,(
    ! [A_620] :
      ( k9_relat_1('#skF_3',A_620) = k2_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4793,c_30])).

tff(c_4803,plain,(
    ! [A_620] : k9_relat_1('#skF_3',A_620) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4438,c_4458,c_4798])).

tff(c_4514,plain,(
    ! [C_567,B_568,A_569] :
      ( ~ v1_xboole_0(C_567)
      | ~ m1_subset_1(B_568,k1_zfmisc_1(C_567))
      | ~ r2_hidden(A_569,B_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4518,plain,(
    ! [A_569] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_569,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4362,c_4514])).

tff(c_4526,plain,(
    ! [A_570] : ~ r2_hidden(A_570,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4300,c_4518])).

tff(c_4531,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_4526])).

tff(c_4759,plain,(
    ! [B_618,A_619] :
      ( k9_relat_1(B_618,A_619) != '#skF_3'
      | ~ r1_tarski(A_619,k1_relat_1(B_618))
      | A_619 = '#skF_3'
      | ~ v1_relat_1(B_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_4288,c_32])).

tff(c_4779,plain,(
    ! [B_618] :
      ( k9_relat_1(B_618,'#skF_5') != '#skF_3'
      | '#skF_5' = '#skF_3'
      | ~ v1_relat_1(B_618) ) ),
    inference(resolution,[status(thm)],[c_4531,c_4759])).

tff(c_4875,plain,(
    ! [B_627] :
      ( k9_relat_1(B_627,'#skF_5') != '#skF_3'
      | ~ v1_relat_1(B_627) ) ),
    inference(splitLeft,[status(thm)],[c_4779])).

tff(c_4884,plain,(
    k9_relat_1('#skF_3','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4438,c_4875])).

tff(c_4893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4803,c_4884])).

tff(c_4894,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4779])).

tff(c_4448,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) = '#skF_3'
      | k1_relat_1(A_23) != '#skF_3'
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_4288,c_38])).

tff(c_4486,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4477,c_4448])).

tff(c_4512,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4486])).

tff(c_4416,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) = '#skF_3'
      | k2_relat_1(A_23) != '#skF_3'
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_4288,c_36])).

tff(c_4487,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | k2_relat_1('#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4477,c_4416])).

tff(c_4513,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4512,c_4487])).

tff(c_4901,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4894,c_4513])).

tff(c_4915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4458,c_4901])).

tff(c_4916,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4486])).

tff(c_5097,plain,(
    ! [C_657,A_658,B_659] :
      ( v4_relat_1(C_657,A_658)
      | ~ m1_subset_1(C_657,k1_zfmisc_1(k2_zfmisc_1(A_658,B_659))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5216,plain,(
    ! [C_678,A_679] :
      ( v4_relat_1(C_678,A_679)
      | ~ m1_subset_1(C_678,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4306,c_5097])).

tff(c_5230,plain,(
    ! [A_680] : v4_relat_1('#skF_5',A_680) ),
    inference(resolution,[status(thm)],[c_4362,c_5216])).

tff(c_5233,plain,(
    ! [A_680] :
      ( k7_relat_1('#skF_5',A_680) = '#skF_5'
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5230,c_34])).

tff(c_5238,plain,(
    ! [A_681] : k7_relat_1('#skF_5',A_681) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4477,c_5233])).

tff(c_5243,plain,(
    ! [A_681] :
      ( k9_relat_1('#skF_5',A_681) = k2_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5238,c_30])).

tff(c_5248,plain,(
    ! [A_681] : k9_relat_1('#skF_5',A_681) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4477,c_4916,c_5243])).

tff(c_4917,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4486])).

tff(c_5302,plain,(
    ! [B_690,A_691] :
      ( k9_relat_1(B_690,A_691) != '#skF_3'
      | ~ r1_tarski(A_691,k1_relat_1(B_690))
      | A_691 = '#skF_3'
      | ~ v1_relat_1(B_690) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4288,c_4288,c_32])).

tff(c_5313,plain,(
    ! [A_691] :
      ( k9_relat_1('#skF_5',A_691) != '#skF_3'
      | ~ r1_tarski(A_691,'#skF_3')
      | A_691 = '#skF_3'
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4917,c_5302])).

tff(c_5332,plain,(
    ! [A_694] :
      ( ~ r1_tarski(A_694,'#skF_3')
      | A_694 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4477,c_5248,c_5313])).

tff(c_5346,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4951,c_5332])).

tff(c_4406,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4295,c_4362,c_4322,c_4295,c_76])).

tff(c_5358,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5346,c_4406])).

tff(c_5757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5753,c_5358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:00:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.24  
% 6.32/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.24  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.32/2.24  
% 6.32/2.24  %Foreground sorts:
% 6.32/2.24  
% 6.32/2.24  
% 6.32/2.24  %Background operators:
% 6.32/2.24  
% 6.32/2.24  
% 6.32/2.24  %Foreground operators:
% 6.32/2.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.32/2.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.32/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.32/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.32/2.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.32/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.32/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.32/2.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.32/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.32/2.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.32/2.24  tff('#skF_2', type, '#skF_2': $i).
% 6.32/2.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.32/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.32/2.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.32/2.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.32/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.32/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.32/2.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.32/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.32/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.32/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.32/2.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.32/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.32/2.24  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.32/2.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.32/2.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.32/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.32/2.24  
% 6.32/2.27  tff(f_150, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 6.32/2.27  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.32/2.27  tff(f_112, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 6.32/2.27  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.32/2.27  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.32/2.27  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.32/2.27  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.32/2.27  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.32/2.27  tff(f_88, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 6.32/2.27  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.32/2.27  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.32/2.27  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.32/2.27  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 6.32/2.27  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.32/2.27  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.32/2.27  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.32/2.27  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 6.32/2.27  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 6.32/2.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.32/2.27  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.32/2.27  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.32/2.27  tff(c_4008, plain, (![A_495, B_496, C_497]: (k2_relset_1(A_495, B_496, C_497)=k2_relat_1(C_497) | ~m1_subset_1(C_497, k1_zfmisc_1(k2_zfmisc_1(A_495, B_496))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.32/2.27  tff(c_4027, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_4008])).
% 6.32/2.27  tff(c_68, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.32/2.27  tff(c_4029, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4027, c_68])).
% 6.32/2.27  tff(c_4151, plain, (![D_520, C_521, B_522, A_523]: (m1_subset_1(D_520, k1_zfmisc_1(k2_zfmisc_1(C_521, B_522))) | ~r1_tarski(k2_relat_1(D_520), B_522) | ~m1_subset_1(D_520, k1_zfmisc_1(k2_zfmisc_1(C_521, A_523))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.32/2.27  tff(c_4246, plain, (![B_538]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_538))) | ~r1_tarski(k2_relat_1('#skF_5'), B_538))), inference(resolution, [status(thm)], [c_70, c_4151])).
% 6.32/2.27  tff(c_66, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.32/2.27  tff(c_99, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_66])).
% 6.32/2.27  tff(c_18, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.32/2.27  tff(c_20, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.32/2.27  tff(c_77, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 6.32/2.27  tff(c_173, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.32/2.27  tff(c_181, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(resolution, [status(thm)], [c_77, c_173])).
% 6.32/2.27  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.32/2.27  tff(c_201, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.32/2.27  tff(c_218, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_201])).
% 6.32/2.27  tff(c_36, plain, (![A_23]: (k1_relat_1(A_23)=k1_xboole_0 | k2_relat_1(A_23)!=k1_xboole_0 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.32/2.27  tff(c_230, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_218, c_36])).
% 6.32/2.27  tff(c_285, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_230])).
% 6.32/2.27  tff(c_561, plain, (![A_126, B_127, C_128]: (k2_relset_1(A_126, B_127, C_128)=k2_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.32/2.27  tff(c_580, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_561])).
% 6.32/2.27  tff(c_582, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_68])).
% 6.32/2.27  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.32/2.27  tff(c_64, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.32/2.27  tff(c_76, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64])).
% 6.32/2.27  tff(c_245, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_76])).
% 6.32/2.27  tff(c_72, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.32/2.27  tff(c_687, plain, (![A_143, B_144, C_145]: (k1_relset_1(A_143, B_144, C_145)=k1_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.32/2.27  tff(c_706, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_687])).
% 6.32/2.27  tff(c_1040, plain, (![B_181, A_182, C_183]: (k1_xboole_0=B_181 | k1_relset_1(A_182, B_181, C_183)=A_182 | ~v1_funct_2(C_183, A_182, B_181) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.32/2.27  tff(c_1050, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_1040])).
% 6.32/2.27  tff(c_1065, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_706, c_1050])).
% 6.32/2.27  tff(c_1066, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_99, c_1065])).
% 6.32/2.27  tff(c_791, plain, (![D_160, C_161, B_162, A_163]: (m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(C_161, B_162))) | ~r1_tarski(k2_relat_1(D_160), B_162) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(C_161, A_163))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.32/2.27  tff(c_833, plain, (![B_169]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_169))) | ~r1_tarski(k2_relat_1('#skF_5'), B_169))), inference(resolution, [status(thm)], [c_70, c_791])).
% 6.32/2.27  tff(c_46, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.32/2.27  tff(c_861, plain, (![B_169]: (k1_relset_1('#skF_2', B_169, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski(k2_relat_1('#skF_5'), B_169))), inference(resolution, [status(thm)], [c_833, c_46])).
% 6.32/2.27  tff(c_1168, plain, (![B_193]: (k1_relset_1('#skF_2', B_193, '#skF_5')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_5'), B_193))), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_861])).
% 6.32/2.27  tff(c_1180, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_582, c_1168])).
% 6.32/2.27  tff(c_805, plain, (![B_162]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_162))) | ~r1_tarski(k2_relat_1('#skF_5'), B_162))), inference(resolution, [status(thm)], [c_70, c_791])).
% 6.32/2.27  tff(c_955, plain, (![B_174, C_175, A_176]: (k1_xboole_0=B_174 | v1_funct_2(C_175, A_176, B_174) | k1_relset_1(A_176, B_174, C_175)!=A_176 | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_174))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.32/2.27  tff(c_1486, plain, (![B_227]: (k1_xboole_0=B_227 | v1_funct_2('#skF_5', '#skF_2', B_227) | k1_relset_1('#skF_2', B_227, '#skF_5')!='#skF_2' | ~r1_tarski(k2_relat_1('#skF_5'), B_227))), inference(resolution, [status(thm)], [c_805, c_955])).
% 6.32/2.27  tff(c_1489, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4') | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_582, c_1486])).
% 6.32/2.27  tff(c_1500, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1180, c_1489])).
% 6.32/2.27  tff(c_1501, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_245, c_1500])).
% 6.32/2.27  tff(c_859, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_833])).
% 6.32/2.27  tff(c_899, plain, (~r1_tarski(k2_relat_1('#skF_5'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_859])).
% 6.32/2.27  tff(c_1525, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_899])).
% 6.32/2.27  tff(c_1565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_582, c_1525])).
% 6.32/2.27  tff(c_1566, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_859])).
% 6.32/2.27  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.32/2.27  tff(c_1596, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_1566, c_22])).
% 6.32/2.27  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.32/2.27  tff(c_231, plain, (![A_67, B_68]: (v1_relat_1(k2_zfmisc_1(A_67, B_68)))), inference(resolution, [status(thm)], [c_77, c_201])).
% 6.32/2.27  tff(c_236, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_231])).
% 6.32/2.27  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.32/2.27  tff(c_123, plain, (![A_48]: (v1_xboole_0(k1_relat_1(A_48)) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.32/2.27  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.32/2.27  tff(c_128, plain, (![A_49]: (k1_relat_1(A_49)=k1_xboole_0 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_123, c_10])).
% 6.32/2.27  tff(c_136, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_128])).
% 6.32/2.27  tff(c_266, plain, (![A_71]: (k2_relat_1(A_71)=k1_xboole_0 | k1_relat_1(A_71)!=k1_xboole_0 | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.32/2.27  tff(c_269, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_236, c_266])).
% 6.32/2.27  tff(c_278, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_136, c_269])).
% 6.32/2.27  tff(c_303, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.32/2.27  tff(c_324, plain, (![A_78, B_79]: (v4_relat_1(k2_zfmisc_1(A_78, B_79), A_78))), inference(resolution, [status(thm)], [c_77, c_303])).
% 6.32/2.27  tff(c_330, plain, (![A_7]: (v4_relat_1(k1_xboole_0, A_7))), inference(superposition, [status(thm), theory('equality')], [c_14, c_324])).
% 6.32/2.27  tff(c_483, plain, (![B_116, A_117]: (k7_relat_1(B_116, A_117)=B_116 | ~v4_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.32/2.27  tff(c_492, plain, (![A_7]: (k7_relat_1(k1_xboole_0, A_7)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_330, c_483])).
% 6.32/2.27  tff(c_520, plain, (![A_118]: (k7_relat_1(k1_xboole_0, A_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_492])).
% 6.32/2.27  tff(c_30, plain, (![B_18, A_17]: (k2_relat_1(k7_relat_1(B_18, A_17))=k9_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.32/2.27  tff(c_525, plain, (![A_118]: (k9_relat_1(k1_xboole_0, A_118)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_520, c_30])).
% 6.32/2.27  tff(c_530, plain, (![A_118]: (k9_relat_1(k1_xboole_0, A_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_278, c_525])).
% 6.32/2.27  tff(c_636, plain, (![B_136, A_137]: (k9_relat_1(B_136, A_137)!=k1_xboole_0 | ~r1_tarski(A_137, k1_relat_1(B_136)) | k1_xboole_0=A_137 | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.32/2.27  tff(c_650, plain, (![A_137]: (k9_relat_1(k1_xboole_0, A_137)!=k1_xboole_0 | ~r1_tarski(A_137, k1_xboole_0) | k1_xboole_0=A_137 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_636])).
% 6.32/2.27  tff(c_654, plain, (![A_137]: (~r1_tarski(A_137, k1_xboole_0) | k1_xboole_0=A_137)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_530, c_650])).
% 6.32/2.27  tff(c_1655, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1596, c_654])).
% 6.32/2.27  tff(c_1704, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1655, c_8])).
% 6.32/2.27  tff(c_1689, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1655, c_1655, c_278])).
% 6.32/2.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.32/2.27  tff(c_331, plain, (![C_80, B_81, A_82]: (~v1_xboole_0(C_80) | ~m1_subset_1(B_81, k1_zfmisc_1(C_80)) | ~r2_hidden(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.32/2.27  tff(c_343, plain, (![A_84, A_85]: (~v1_xboole_0(A_84) | ~r2_hidden(A_85, A_84))), inference(resolution, [status(thm)], [c_77, c_331])).
% 6.32/2.27  tff(c_347, plain, (![A_1, B_2]: (~v1_xboole_0(A_1) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_343])).
% 6.32/2.27  tff(c_42, plain, (![C_29, B_28, A_27]: (v5_relat_1(C_29, B_28) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.32/2.27  tff(c_870, plain, (![B_170]: (v5_relat_1('#skF_5', B_170) | ~r1_tarski(k2_relat_1('#skF_5'), B_170))), inference(resolution, [status(thm)], [c_833, c_42])).
% 6.32/2.27  tff(c_883, plain, (![B_2]: (v5_relat_1('#skF_5', B_2) | ~v1_xboole_0(k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_347, c_870])).
% 6.32/2.27  tff(c_898, plain, (~v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_883])).
% 6.32/2.27  tff(c_1772, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1689, c_898])).
% 6.32/2.27  tff(c_1779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1704, c_1772])).
% 6.32/2.27  tff(c_1781, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_883])).
% 6.32/2.27  tff(c_1829, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_1781, c_10])).
% 6.32/2.27  tff(c_1838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_1829])).
% 6.32/2.27  tff(c_1839, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_230])).
% 6.32/2.27  tff(c_280, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_218, c_266])).
% 6.32/2.27  tff(c_1854, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1839, c_280])).
% 6.32/2.27  tff(c_2384, plain, (![D_323, C_324, B_325, A_326]: (m1_subset_1(D_323, k1_zfmisc_1(k2_zfmisc_1(C_324, B_325))) | ~r1_tarski(k2_relat_1(D_323), B_325) | ~m1_subset_1(D_323, k1_zfmisc_1(k2_zfmisc_1(C_324, A_326))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.32/2.27  tff(c_2389, plain, (![B_325]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_325))) | ~r1_tarski(k2_relat_1('#skF_5'), B_325))), inference(resolution, [status(thm)], [c_70, c_2384])).
% 6.32/2.27  tff(c_2424, plain, (![B_329]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_329))) | ~r1_tarski(k1_xboole_0, B_329))), inference(demodulation, [status(thm), theory('equality')], [c_1854, c_2389])).
% 6.32/2.27  tff(c_2450, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_2424])).
% 6.32/2.27  tff(c_2465, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_2450])).
% 6.32/2.27  tff(c_2485, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_2465, c_22])).
% 6.32/2.27  tff(c_1954, plain, (![C_260, A_261, B_262]: (v4_relat_1(C_260, A_261) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.32/2.27  tff(c_1985, plain, (![A_263, B_264]: (v4_relat_1(k2_zfmisc_1(A_263, B_264), A_263))), inference(resolution, [status(thm)], [c_77, c_1954])).
% 6.32/2.27  tff(c_2026, plain, (![A_268]: (v4_relat_1(k1_xboole_0, A_268))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1985])).
% 6.32/2.27  tff(c_34, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.32/2.27  tff(c_2029, plain, (![A_268]: (k7_relat_1(k1_xboole_0, A_268)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2026, c_34])).
% 6.32/2.27  tff(c_2032, plain, (![A_268]: (k7_relat_1(k1_xboole_0, A_268)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_2029])).
% 6.32/2.27  tff(c_2058, plain, (![B_276, A_277]: (k2_relat_1(k7_relat_1(B_276, A_277))=k9_relat_1(B_276, A_277) | ~v1_relat_1(B_276))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.32/2.27  tff(c_2067, plain, (![A_268]: (k9_relat_1(k1_xboole_0, A_268)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2032, c_2058])).
% 6.32/2.27  tff(c_2074, plain, (![A_268]: (k9_relat_1(k1_xboole_0, A_268)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_278, c_2067])).
% 6.32/2.27  tff(c_2200, plain, (![B_297, A_298]: (k9_relat_1(B_297, A_298)!=k1_xboole_0 | ~r1_tarski(A_298, k1_relat_1(B_297)) | k1_xboole_0=A_298 | ~v1_relat_1(B_297))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.32/2.27  tff(c_2217, plain, (![A_298]: (k9_relat_1(k1_xboole_0, A_298)!=k1_xboole_0 | ~r1_tarski(A_298, k1_xboole_0) | k1_xboole_0=A_298 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_2200])).
% 6.32/2.27  tff(c_2223, plain, (![A_298]: (~r1_tarski(A_298, k1_xboole_0) | k1_xboole_0=A_298)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_2074, c_2217])).
% 6.32/2.27  tff(c_2523, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2485, c_2223])).
% 6.32/2.27  tff(c_2566, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_99])).
% 6.32/2.27  tff(c_2150, plain, (![A_288, B_289, C_290]: (k1_relset_1(A_288, B_289, C_290)=k1_relat_1(C_290) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.32/2.27  tff(c_2157, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_70, c_2150])).
% 6.32/2.27  tff(c_2170, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1839, c_2157])).
% 6.32/2.27  tff(c_2541, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_2170])).
% 6.32/2.27  tff(c_62, plain, (![B_41, A_40, C_42]: (k1_xboole_0=B_41 | k1_relset_1(A_40, B_41, C_42)=A_40 | ~v1_funct_2(C_42, A_40, B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.32/2.27  tff(c_2672, plain, (![B_340, A_341, C_342]: (B_340='#skF_5' | k1_relset_1(A_341, B_340, C_342)=A_341 | ~v1_funct_2(C_342, A_341, B_340) | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_341, B_340))))), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_62])).
% 6.32/2.27  tff(c_2679, plain, ('#skF_5'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_2672])).
% 6.32/2.27  tff(c_2687, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2541, c_2679])).
% 6.32/2.27  tff(c_2688, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2566, c_2687])).
% 6.32/2.27  tff(c_2568, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_8])).
% 6.32/2.27  tff(c_2701, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_2568])).
% 6.32/2.27  tff(c_2564, plain, (![B_8]: (k2_zfmisc_1('#skF_5', B_8)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_2523, c_16])).
% 6.32/2.27  tff(c_2809, plain, (![B_8]: (k2_zfmisc_1('#skF_2', B_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2688, c_2688, c_2564])).
% 6.32/2.27  tff(c_1876, plain, (![C_243, B_244, A_245]: (~v1_xboole_0(C_243) | ~m1_subset_1(B_244, k1_zfmisc_1(C_243)) | ~r2_hidden(A_245, B_244))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.32/2.27  tff(c_1884, plain, (![A_245]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_245, '#skF_5'))), inference(resolution, [status(thm)], [c_70, c_1876])).
% 6.32/2.27  tff(c_1935, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1884])).
% 6.32/2.27  tff(c_2810, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2809, c_1935])).
% 6.32/2.27  tff(c_2813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2701, c_2810])).
% 6.32/2.27  tff(c_2815, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1884])).
% 6.32/2.27  tff(c_2852, plain, (k2_zfmisc_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2815, c_10])).
% 6.32/2.27  tff(c_12, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.32/2.27  tff(c_2865, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2852, c_12])).
% 6.32/2.27  tff(c_2871, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_99, c_2865])).
% 6.32/2.27  tff(c_2885, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2871, c_2871, c_136])).
% 6.32/2.27  tff(c_2887, plain, (![B_8]: (k2_zfmisc_1('#skF_2', B_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2871, c_2871, c_16])).
% 6.32/2.27  tff(c_3183, plain, (![A_383, B_384, C_385]: (k1_relset_1(A_383, B_384, C_385)=k1_relat_1(C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.32/2.27  tff(c_3641, plain, (![A_444, B_445]: (k1_relset_1(A_444, B_445, k2_zfmisc_1(A_444, B_445))=k1_relat_1(k2_zfmisc_1(A_444, B_445)))), inference(resolution, [status(thm)], [c_77, c_3183])).
% 6.32/2.27  tff(c_3653, plain, (![B_8]: (k1_relat_1(k2_zfmisc_1('#skF_2', B_8))=k1_relset_1('#skF_2', B_8, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2887, c_3641])).
% 6.32/2.27  tff(c_3657, plain, (![B_8]: (k1_relset_1('#skF_2', B_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2885, c_2887, c_3653])).
% 6.32/2.27  tff(c_56, plain, (![C_42, B_41]: (v1_funct_2(C_42, k1_xboole_0, B_41) | k1_relset_1(k1_xboole_0, B_41, C_42)!=k1_xboole_0 | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_41))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.32/2.27  tff(c_79, plain, (![C_42, B_41]: (v1_funct_2(C_42, k1_xboole_0, B_41) | k1_relset_1(k1_xboole_0, B_41, C_42)!=k1_xboole_0 | ~m1_subset_1(C_42, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_56])).
% 6.32/2.27  tff(c_3457, plain, (![C_417, B_418]: (v1_funct_2(C_417, '#skF_2', B_418) | k1_relset_1('#skF_2', B_418, C_417)!='#skF_2' | ~m1_subset_1(C_417, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2871, c_2871, c_2871, c_2871, c_79])).
% 6.32/2.27  tff(c_3607, plain, (![B_441]: (v1_funct_2('#skF_2', '#skF_2', B_441) | k1_relset_1('#skF_2', B_441, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_77, c_3457])).
% 6.32/2.27  tff(c_2820, plain, (![A_354]: (~r2_hidden(A_354, '#skF_5'))), inference(splitRight, [status(thm)], [c_1884])).
% 6.32/2.27  tff(c_2825, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_2820])).
% 6.32/2.27  tff(c_2880, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2871, c_236])).
% 6.32/2.27  tff(c_2876, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2871, c_2871, c_278])).
% 6.32/2.27  tff(c_2888, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2871, c_2871, c_14])).
% 6.32/2.27  tff(c_2913, plain, (![C_356, A_357, B_358]: (v4_relat_1(C_356, A_357) | ~m1_subset_1(C_356, k1_zfmisc_1(k2_zfmisc_1(A_357, B_358))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.32/2.27  tff(c_3010, plain, (![A_362, B_363]: (v4_relat_1(k2_zfmisc_1(A_362, B_363), A_362))), inference(resolution, [status(thm)], [c_77, c_2913])).
% 6.32/2.27  tff(c_3040, plain, (![A_367]: (v4_relat_1('#skF_2', A_367))), inference(superposition, [status(thm), theory('equality')], [c_2888, c_3010])).
% 6.32/2.27  tff(c_3043, plain, (![A_367]: (k7_relat_1('#skF_2', A_367)='#skF_2' | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_3040, c_34])).
% 6.32/2.27  tff(c_3046, plain, (![A_367]: (k7_relat_1('#skF_2', A_367)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2880, c_3043])).
% 6.32/2.27  tff(c_3093, plain, (![B_374, A_375]: (k2_relat_1(k7_relat_1(B_374, A_375))=k9_relat_1(B_374, A_375) | ~v1_relat_1(B_374))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.32/2.27  tff(c_3102, plain, (![A_367]: (k9_relat_1('#skF_2', A_367)=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3046, c_3093])).
% 6.32/2.27  tff(c_3106, plain, (![A_367]: (k9_relat_1('#skF_2', A_367)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2880, c_2876, c_3102])).
% 6.32/2.27  tff(c_32, plain, (![B_20, A_19]: (k9_relat_1(B_20, A_19)!=k1_xboole_0 | ~r1_tarski(A_19, k1_relat_1(B_20)) | k1_xboole_0=A_19 | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.32/2.27  tff(c_3340, plain, (![B_412, A_413]: (k9_relat_1(B_412, A_413)!='#skF_2' | ~r1_tarski(A_413, k1_relat_1(B_412)) | A_413='#skF_2' | ~v1_relat_1(B_412))), inference(demodulation, [status(thm), theory('equality')], [c_2871, c_2871, c_32])).
% 6.32/2.27  tff(c_3346, plain, (![A_413]: (k9_relat_1('#skF_2', A_413)!='#skF_2' | ~r1_tarski(A_413, '#skF_2') | A_413='#skF_2' | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2885, c_3340])).
% 6.32/2.27  tff(c_3369, plain, (![A_414]: (~r1_tarski(A_414, '#skF_2') | A_414='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2880, c_3106, c_3346])).
% 6.32/2.27  tff(c_3382, plain, ('#skF_5'='#skF_2'), inference(resolution, [status(thm)], [c_2825, c_3369])).
% 6.32/2.27  tff(c_3395, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3382, c_245])).
% 6.32/2.27  tff(c_3619, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_2')!='#skF_2'), inference(resolution, [status(thm)], [c_3607, c_3395])).
% 6.32/2.27  tff(c_3690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3657, c_3619])).
% 6.32/2.27  tff(c_3691, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_76])).
% 6.32/2.27  tff(c_4265, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4246, c_3691])).
% 6.32/2.27  tff(c_4286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4029, c_4265])).
% 6.32/2.27  tff(c_4288, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_66])).
% 6.32/2.27  tff(c_4287, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_66])).
% 6.32/2.27  tff(c_4295, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_4287])).
% 6.32/2.27  tff(c_4290, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4287, c_8])).
% 6.32/2.27  tff(c_4300, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4295, c_4290])).
% 6.32/2.27  tff(c_4339, plain, (![A_543]: (v1_xboole_0(k1_relat_1(A_543)) | ~v1_xboole_0(A_543))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.32/2.27  tff(c_4289, plain, (![A_6]: (A_6='#skF_2' | ~v1_xboole_0(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_4287, c_10])).
% 6.32/2.27  tff(c_4315, plain, (![A_6]: (A_6='#skF_3' | ~v1_xboole_0(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_4295, c_4289])).
% 6.32/2.27  tff(c_4344, plain, (![A_544]: (k1_relat_1(A_544)='#skF_3' | ~v1_xboole_0(A_544))), inference(resolution, [status(thm)], [c_4339, c_4315])).
% 6.32/2.27  tff(c_4352, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_4300, c_4344])).
% 6.32/2.27  tff(c_4322, plain, (![B_8]: (k2_zfmisc_1('#skF_3', B_8)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_4288, c_16])).
% 6.32/2.27  tff(c_5494, plain, (![A_707, B_708, C_709]: (k1_relset_1(A_707, B_708, C_709)=k1_relat_1(C_709) | ~m1_subset_1(C_709, k1_zfmisc_1(k2_zfmisc_1(A_707, B_708))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.32/2.27  tff(c_5649, plain, (![A_730, B_731]: (k1_relset_1(A_730, B_731, k2_zfmisc_1(A_730, B_731))=k1_relat_1(k2_zfmisc_1(A_730, B_731)))), inference(resolution, [status(thm)], [c_77, c_5494])).
% 6.32/2.27  tff(c_5658, plain, (![B_8]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_8))=k1_relset_1('#skF_3', B_8, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4322, c_5649])).
% 6.32/2.27  tff(c_5664, plain, (![B_8]: (k1_relset_1('#skF_3', B_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4352, c_4322, c_5658])).
% 6.32/2.27  tff(c_5743, plain, (![C_743, B_744]: (v1_funct_2(C_743, '#skF_3', B_744) | k1_relset_1('#skF_3', B_744, C_743)!='#skF_3' | ~m1_subset_1(C_743, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_4288, c_4288, c_4288, c_79])).
% 6.32/2.27  tff(c_5749, plain, (![B_744]: (v1_funct_2('#skF_3', '#skF_3', B_744) | k1_relset_1('#skF_3', B_744, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_77, c_5743])).
% 6.32/2.27  tff(c_5753, plain, (![B_744]: (v1_funct_2('#skF_3', '#skF_3', B_744))), inference(demodulation, [status(thm), theory('equality')], [c_5664, c_5749])).
% 6.32/2.27  tff(c_4306, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_4288, c_14])).
% 6.32/2.27  tff(c_4362, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4306, c_4295, c_70])).
% 6.32/2.27  tff(c_4934, plain, (![C_628, B_629, A_630]: (~v1_xboole_0(C_628) | ~m1_subset_1(B_629, k1_zfmisc_1(C_628)) | ~r2_hidden(A_630, B_629))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.32/2.27  tff(c_4938, plain, (![A_630]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_630, '#skF_5'))), inference(resolution, [status(thm)], [c_4362, c_4934])).
% 6.32/2.27  tff(c_4946, plain, (![A_631]: (~r2_hidden(A_631, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4300, c_4938])).
% 6.32/2.27  tff(c_4951, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_4946])).
% 6.32/2.27  tff(c_4418, plain, (![C_557, A_558, B_559]: (v1_relat_1(C_557) | ~m1_subset_1(C_557, k1_zfmisc_1(k2_zfmisc_1(A_558, B_559))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.32/2.27  tff(c_4464, plain, (![C_563]: (v1_relat_1(C_563) | ~m1_subset_1(C_563, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4322, c_4418])).
% 6.32/2.27  tff(c_4477, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4362, c_4464])).
% 6.32/2.27  tff(c_4433, plain, (![A_560, B_561]: (v1_relat_1(k2_zfmisc_1(A_560, B_561)))), inference(resolution, [status(thm)], [c_77, c_4418])).
% 6.32/2.27  tff(c_4438, plain, (v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4322, c_4433])).
% 6.32/2.27  tff(c_38, plain, (![A_23]: (k2_relat_1(A_23)=k1_xboole_0 | k1_relat_1(A_23)!=k1_xboole_0 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.32/2.27  tff(c_4449, plain, (![A_562]: (k2_relat_1(A_562)='#skF_3' | k1_relat_1(A_562)!='#skF_3' | ~v1_relat_1(A_562))), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_4288, c_38])).
% 6.32/2.27  tff(c_4452, plain, (k2_relat_1('#skF_3')='#skF_3' | k1_relat_1('#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_4438, c_4449])).
% 6.32/2.27  tff(c_4458, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4352, c_4452])).
% 6.32/2.27  tff(c_4700, plain, (![C_610, A_611, B_612]: (v4_relat_1(C_610, A_611) | ~m1_subset_1(C_610, k1_zfmisc_1(k2_zfmisc_1(A_611, B_612))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.32/2.27  tff(c_4731, plain, (![A_615, B_616]: (v4_relat_1(k2_zfmisc_1(A_615, B_616), A_615))), inference(resolution, [status(thm)], [c_77, c_4700])).
% 6.32/2.27  tff(c_4751, plain, (![A_617]: (v4_relat_1('#skF_3', A_617))), inference(superposition, [status(thm), theory('equality')], [c_4306, c_4731])).
% 6.32/2.27  tff(c_4754, plain, (![A_617]: (k7_relat_1('#skF_3', A_617)='#skF_3' | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4751, c_34])).
% 6.32/2.27  tff(c_4793, plain, (![A_620]: (k7_relat_1('#skF_3', A_620)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4438, c_4754])).
% 6.32/2.27  tff(c_4798, plain, (![A_620]: (k9_relat_1('#skF_3', A_620)=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4793, c_30])).
% 6.32/2.27  tff(c_4803, plain, (![A_620]: (k9_relat_1('#skF_3', A_620)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4438, c_4458, c_4798])).
% 6.32/2.27  tff(c_4514, plain, (![C_567, B_568, A_569]: (~v1_xboole_0(C_567) | ~m1_subset_1(B_568, k1_zfmisc_1(C_567)) | ~r2_hidden(A_569, B_568))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.32/2.27  tff(c_4518, plain, (![A_569]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_569, '#skF_5'))), inference(resolution, [status(thm)], [c_4362, c_4514])).
% 6.32/2.27  tff(c_4526, plain, (![A_570]: (~r2_hidden(A_570, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4300, c_4518])).
% 6.32/2.27  tff(c_4531, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_4526])).
% 6.32/2.27  tff(c_4759, plain, (![B_618, A_619]: (k9_relat_1(B_618, A_619)!='#skF_3' | ~r1_tarski(A_619, k1_relat_1(B_618)) | A_619='#skF_3' | ~v1_relat_1(B_618))), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_4288, c_32])).
% 6.32/2.27  tff(c_4779, plain, (![B_618]: (k9_relat_1(B_618, '#skF_5')!='#skF_3' | '#skF_5'='#skF_3' | ~v1_relat_1(B_618))), inference(resolution, [status(thm)], [c_4531, c_4759])).
% 6.32/2.27  tff(c_4875, plain, (![B_627]: (k9_relat_1(B_627, '#skF_5')!='#skF_3' | ~v1_relat_1(B_627))), inference(splitLeft, [status(thm)], [c_4779])).
% 6.32/2.27  tff(c_4884, plain, (k9_relat_1('#skF_3', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_4438, c_4875])).
% 6.32/2.27  tff(c_4893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4803, c_4884])).
% 6.32/2.27  tff(c_4894, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_4779])).
% 6.32/2.27  tff(c_4448, plain, (![A_23]: (k2_relat_1(A_23)='#skF_3' | k1_relat_1(A_23)!='#skF_3' | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_4288, c_38])).
% 6.32/2.27  tff(c_4486, plain, (k2_relat_1('#skF_5')='#skF_3' | k1_relat_1('#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_4477, c_4448])).
% 6.32/2.27  tff(c_4512, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_4486])).
% 6.32/2.27  tff(c_4416, plain, (![A_23]: (k1_relat_1(A_23)='#skF_3' | k2_relat_1(A_23)!='#skF_3' | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_4288, c_36])).
% 6.32/2.27  tff(c_4487, plain, (k1_relat_1('#skF_5')='#skF_3' | k2_relat_1('#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_4477, c_4416])).
% 6.32/2.27  tff(c_4513, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4512, c_4487])).
% 6.32/2.27  tff(c_4901, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4894, c_4513])).
% 6.32/2.27  tff(c_4915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4458, c_4901])).
% 6.32/2.27  tff(c_4916, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_4486])).
% 6.32/2.27  tff(c_5097, plain, (![C_657, A_658, B_659]: (v4_relat_1(C_657, A_658) | ~m1_subset_1(C_657, k1_zfmisc_1(k2_zfmisc_1(A_658, B_659))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.32/2.27  tff(c_5216, plain, (![C_678, A_679]: (v4_relat_1(C_678, A_679) | ~m1_subset_1(C_678, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4306, c_5097])).
% 6.32/2.27  tff(c_5230, plain, (![A_680]: (v4_relat_1('#skF_5', A_680))), inference(resolution, [status(thm)], [c_4362, c_5216])).
% 6.32/2.27  tff(c_5233, plain, (![A_680]: (k7_relat_1('#skF_5', A_680)='#skF_5' | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_5230, c_34])).
% 6.32/2.27  tff(c_5238, plain, (![A_681]: (k7_relat_1('#skF_5', A_681)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4477, c_5233])).
% 6.32/2.27  tff(c_5243, plain, (![A_681]: (k9_relat_1('#skF_5', A_681)=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5238, c_30])).
% 6.32/2.27  tff(c_5248, plain, (![A_681]: (k9_relat_1('#skF_5', A_681)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4477, c_4916, c_5243])).
% 6.32/2.27  tff(c_4917, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_4486])).
% 6.32/2.27  tff(c_5302, plain, (![B_690, A_691]: (k9_relat_1(B_690, A_691)!='#skF_3' | ~r1_tarski(A_691, k1_relat_1(B_690)) | A_691='#skF_3' | ~v1_relat_1(B_690))), inference(demodulation, [status(thm), theory('equality')], [c_4288, c_4288, c_32])).
% 6.32/2.27  tff(c_5313, plain, (![A_691]: (k9_relat_1('#skF_5', A_691)!='#skF_3' | ~r1_tarski(A_691, '#skF_3') | A_691='#skF_3' | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4917, c_5302])).
% 6.32/2.27  tff(c_5332, plain, (![A_694]: (~r1_tarski(A_694, '#skF_3') | A_694='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4477, c_5248, c_5313])).
% 6.32/2.27  tff(c_5346, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_4951, c_5332])).
% 6.32/2.27  tff(c_4406, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4295, c_4362, c_4322, c_4295, c_76])).
% 6.32/2.27  tff(c_5358, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5346, c_4406])).
% 6.32/2.27  tff(c_5757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5753, c_5358])).
% 6.32/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.27  
% 6.32/2.27  Inference rules
% 6.32/2.27  ----------------------
% 6.32/2.27  #Ref     : 0
% 6.32/2.27  #Sup     : 1203
% 6.32/2.27  #Fact    : 0
% 6.32/2.27  #Define  : 0
% 6.32/2.27  #Split   : 21
% 6.32/2.27  #Chain   : 0
% 6.32/2.27  #Close   : 0
% 6.32/2.27  
% 6.32/2.27  Ordering : KBO
% 6.32/2.27  
% 6.32/2.27  Simplification rules
% 6.32/2.27  ----------------------
% 6.32/2.27  #Subsume      : 150
% 6.32/2.27  #Demod        : 1076
% 6.32/2.28  #Tautology    : 648
% 6.32/2.28  #SimpNegUnit  : 14
% 6.32/2.28  #BackRed      : 244
% 6.32/2.28  
% 6.32/2.28  #Partial instantiations: 0
% 6.32/2.28  #Strategies tried      : 1
% 6.32/2.28  
% 6.32/2.28  Timing (in seconds)
% 6.32/2.28  ----------------------
% 6.32/2.28  Preprocessing        : 0.36
% 6.32/2.28  Parsing              : 0.19
% 6.32/2.28  CNF conversion       : 0.03
% 6.32/2.28  Main loop            : 1.08
% 6.32/2.28  Inferencing          : 0.38
% 6.32/2.28  Reduction            : 0.36
% 6.32/2.28  Demodulation         : 0.25
% 6.32/2.28  BG Simplification    : 0.04
% 6.32/2.28  Subsumption          : 0.19
% 6.32/2.28  Abstraction          : 0.04
% 6.32/2.28  MUC search           : 0.00
% 6.32/2.28  Cooper               : 0.00
% 6.32/2.28  Total                : 1.53
% 6.32/2.28  Index Insertion      : 0.00
% 6.32/2.28  Index Deletion       : 0.00
% 6.32/2.28  Index Matching       : 0.00
% 6.32/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
