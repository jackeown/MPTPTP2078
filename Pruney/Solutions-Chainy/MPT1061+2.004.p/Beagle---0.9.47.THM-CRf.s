%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:36 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 289 expanded)
%              Number of leaves         :   37 ( 113 expanded)
%              Depth                    :   12
%              Number of atoms          :  207 ( 946 expanded)
%              Number of equality atoms :   22 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
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

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(C,A)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(A,B,D,C))
            & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
            & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_50,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_666,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( k2_partfun1(A_185,B_186,C_187,D_188) = k7_relat_1(C_187,D_188)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ v1_funct_1(C_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_670,plain,(
    ! [D_188] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_188) = k7_relat_1('#skF_5',D_188)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_666])).

tff(c_676,plain,(
    ! [D_188] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_188) = k7_relat_1('#skF_5',D_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_670])).

tff(c_1210,plain,(
    ! [B_284,A_285,D_286,C_287] :
      ( k1_xboole_0 = B_284
      | v1_funct_2(k2_partfun1(A_285,B_284,D_286,C_287),C_287,B_284)
      | ~ r1_tarski(C_287,A_285)
      | ~ m1_subset_1(D_286,k1_zfmisc_1(k2_zfmisc_1(A_285,B_284)))
      | ~ v1_funct_2(D_286,A_285,B_284)
      | ~ v1_funct_1(D_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1230,plain,(
    ! [C_287] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5',C_287),C_287,'#skF_4')
      | ~ r1_tarski(C_287,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_1210])).

tff(c_1250,plain,(
    ! [C_287] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(k7_relat_1('#skF_5',C_287),C_287,'#skF_4')
      | ~ r1_tarski(C_287,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_676,c_1230])).

tff(c_1252,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1250])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1256,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_2])).

tff(c_1258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1256])).

tff(c_1259,plain,(
    ! [C_287] :
      ( v1_funct_2(k7_relat_1('#skF_5',C_287),C_287,'#skF_4')
      | ~ r1_tarski(C_287,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_1250])).

tff(c_570,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( v1_funct_1(k2_partfun1(A_159,B_160,C_161,D_162))
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_574,plain,(
    ! [D_162] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_162))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_570])).

tff(c_580,plain,(
    ! [D_162] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_162)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_574])).

tff(c_679,plain,(
    ! [D_162] : v1_funct_1(k7_relat_1('#skF_5',D_162)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_580])).

tff(c_1260,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1250])).

tff(c_1319,plain,(
    ! [B_296,A_297,D_298,C_299] :
      ( k1_xboole_0 = B_296
      | m1_subset_1(k2_partfun1(A_297,B_296,D_298,C_299),k1_zfmisc_1(k2_zfmisc_1(C_299,B_296)))
      | ~ r1_tarski(C_299,A_297)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(A_297,B_296)))
      | ~ v1_funct_2(D_298,A_297,B_296)
      | ~ v1_funct_1(D_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1357,plain,(
    ! [D_188] :
      ( k1_xboole_0 = '#skF_4'
      | m1_subset_1(k7_relat_1('#skF_5',D_188),k1_zfmisc_1(k2_zfmisc_1(D_188,'#skF_4')))
      | ~ r1_tarski(D_188,'#skF_1')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_1319])).

tff(c_1379,plain,(
    ! [D_188] :
      ( k1_xboole_0 = '#skF_4'
      | m1_subset_1(k7_relat_1('#skF_5',D_188),k1_zfmisc_1(k2_zfmisc_1(D_188,'#skF_4')))
      | ~ r1_tarski(D_188,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1357])).

tff(c_1381,plain,(
    ! [D_300] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_300),k1_zfmisc_1(k2_zfmisc_1(D_300,'#skF_4')))
      | ~ r1_tarski(D_300,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1260,c_1379])).

tff(c_24,plain,(
    ! [C_29,A_26,B_27] :
      ( v1_partfun1(C_29,A_26)
      | ~ v1_funct_2(C_29,A_26,B_27)
      | ~ v1_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | v1_xboole_0(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1395,plain,(
    ! [D_300] :
      ( v1_partfun1(k7_relat_1('#skF_5',D_300),D_300)
      | ~ v1_funct_2(k7_relat_1('#skF_5',D_300),D_300,'#skF_4')
      | ~ v1_funct_1(k7_relat_1('#skF_5',D_300))
      | v1_xboole_0('#skF_4')
      | ~ r1_tarski(D_300,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1381,c_24])).

tff(c_1424,plain,(
    ! [D_300] :
      ( v1_partfun1(k7_relat_1('#skF_5',D_300),D_300)
      | ~ v1_funct_2(k7_relat_1('#skF_5',D_300),D_300,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r1_tarski(D_300,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_1395])).

tff(c_1451,plain,(
    ! [D_305] :
      ( v1_partfun1(k7_relat_1('#skF_5',D_305),D_305)
      | ~ v1_funct_2(k7_relat_1('#skF_5',D_305),D_305,'#skF_4')
      | ~ r1_tarski(D_305,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1424])).

tff(c_1461,plain,(
    ! [C_306] :
      ( v1_partfun1(k7_relat_1('#skF_5',C_306),C_306)
      | ~ r1_tarski(C_306,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1259,c_1451])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_92])).

tff(c_98,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_95])).

tff(c_108,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( k7_relset_1(A_63,B_64,C_65,D_66) = k9_relat_1(C_65,D_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_111,plain,(
    ! [D_66] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_66) = k9_relat_1('#skF_5',D_66) ),
    inference(resolution,[status(thm)],[c_52,c_108])).

tff(c_48,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_120,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_48])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_184,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k2_partfun1(A_88,B_89,C_90,D_91) = k7_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_186,plain,(
    ! [D_91] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_91) = k7_relat_1('#skF_5',D_91)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_184])).

tff(c_189,plain,(
    ! [D_91] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_91) = k7_relat_1('#skF_5',D_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_186])).

tff(c_287,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( m1_subset_1(k2_partfun1(A_104,B_105,C_106,D_107),k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_305,plain,(
    ! [D_91] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_91),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_287])).

tff(c_316,plain,(
    ! [D_108] : m1_subset_1(k7_relat_1('#skF_5',D_108),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_305])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_331,plain,(
    ! [D_108] :
      ( v1_relat_1(k7_relat_1('#skF_5',D_108))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_316,c_4])).

tff(c_348,plain,(
    ! [D_108] : v1_relat_1(k7_relat_1('#skF_5',D_108)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_331])).

tff(c_202,plain,(
    ! [C_94,A_95,B_96] :
      ( m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ r1_tarski(k2_relat_1(C_94),B_96)
      | ~ r1_tarski(k1_relat_1(C_94),A_95)
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_79,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( v1_funct_1(k2_partfun1(A_53,B_54,C_55,D_56))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_81,plain,(
    ! [D_56] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_56))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_79])).

tff(c_84,plain,(
    ! [D_56] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_81])).

tff(c_46,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_61,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_61])).

tff(c_88,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_91,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_191,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_91])).

tff(c_226,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_202,c_191])).

tff(c_526,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_226])).

tff(c_527,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_530,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_527])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_530])).

tff(c_535,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_542,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_535])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_120,c_542])).

tff(c_546,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_547,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_614,plain,(
    ! [C_174,A_175,B_176] :
      ( v1_funct_2(C_174,A_175,B_176)
      | ~ v1_partfun1(C_174,A_175)
      | ~ v1_funct_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_617,plain,
    ( v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_partfun1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_547,c_614])).

tff(c_623,plain,
    ( v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_partfun1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_617])).

tff(c_624,plain,(
    ~ v1_partfun1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_546,c_623])).

tff(c_677,plain,(
    ~ v1_partfun1(k7_relat_1('#skF_5','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_624])).

tff(c_1464,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_1461,c_677])).

tff(c_1468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.61  
% 3.47/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.62  %$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.47/1.62  
% 3.47/1.62  %Foreground sorts:
% 3.47/1.62  
% 3.47/1.62  
% 3.47/1.62  %Background operators:
% 3.47/1.62  
% 3.47/1.62  
% 3.47/1.62  %Foreground operators:
% 3.47/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.47/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.47/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.47/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.47/1.62  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.47/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.47/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.62  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.47/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.62  
% 3.85/1.64  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 3.85/1.64  tff(f_103, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.85/1.64  tff(f_122, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 3.85/1.64  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.85/1.64  tff(f_97, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.85/1.64  tff(f_89, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.85/1.64  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.85/1.64  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.85/1.64  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.85/1.64  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.85/1.64  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.85/1.64  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.85/1.64  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.85/1.64  tff(c_50, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.85/1.64  tff(c_58, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.85/1.64  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.85/1.64  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.85/1.64  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.85/1.64  tff(c_666, plain, (![A_185, B_186, C_187, D_188]: (k2_partfun1(A_185, B_186, C_187, D_188)=k7_relat_1(C_187, D_188) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~v1_funct_1(C_187))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.64  tff(c_670, plain, (![D_188]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_188)=k7_relat_1('#skF_5', D_188) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_666])).
% 3.85/1.64  tff(c_676, plain, (![D_188]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_188)=k7_relat_1('#skF_5', D_188))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_670])).
% 3.85/1.64  tff(c_1210, plain, (![B_284, A_285, D_286, C_287]: (k1_xboole_0=B_284 | v1_funct_2(k2_partfun1(A_285, B_284, D_286, C_287), C_287, B_284) | ~r1_tarski(C_287, A_285) | ~m1_subset_1(D_286, k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))) | ~v1_funct_2(D_286, A_285, B_284) | ~v1_funct_1(D_286))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.64  tff(c_1230, plain, (![C_287]: (k1_xboole_0='#skF_4' | v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', C_287), C_287, '#skF_4') | ~r1_tarski(C_287, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_1210])).
% 3.85/1.64  tff(c_1250, plain, (![C_287]: (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_5', C_287), C_287, '#skF_4') | ~r1_tarski(C_287, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_676, c_1230])).
% 3.85/1.64  tff(c_1252, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1250])).
% 3.85/1.64  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.85/1.64  tff(c_1256, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1252, c_2])).
% 3.85/1.64  tff(c_1258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1256])).
% 3.85/1.64  tff(c_1259, plain, (![C_287]: (v1_funct_2(k7_relat_1('#skF_5', C_287), C_287, '#skF_4') | ~r1_tarski(C_287, '#skF_1'))), inference(splitRight, [status(thm)], [c_1250])).
% 3.85/1.64  tff(c_570, plain, (![A_159, B_160, C_161, D_162]: (v1_funct_1(k2_partfun1(A_159, B_160, C_161, D_162)) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_1(C_161))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.85/1.64  tff(c_574, plain, (![D_162]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_162)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_570])).
% 3.85/1.64  tff(c_580, plain, (![D_162]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_162)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_574])).
% 3.85/1.64  tff(c_679, plain, (![D_162]: (v1_funct_1(k7_relat_1('#skF_5', D_162)))), inference(demodulation, [status(thm), theory('equality')], [c_676, c_580])).
% 3.85/1.64  tff(c_1260, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1250])).
% 3.85/1.64  tff(c_1319, plain, (![B_296, A_297, D_298, C_299]: (k1_xboole_0=B_296 | m1_subset_1(k2_partfun1(A_297, B_296, D_298, C_299), k1_zfmisc_1(k2_zfmisc_1(C_299, B_296))) | ~r1_tarski(C_299, A_297) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(A_297, B_296))) | ~v1_funct_2(D_298, A_297, B_296) | ~v1_funct_1(D_298))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.85/1.64  tff(c_1357, plain, (![D_188]: (k1_xboole_0='#skF_4' | m1_subset_1(k7_relat_1('#skF_5', D_188), k1_zfmisc_1(k2_zfmisc_1(D_188, '#skF_4'))) | ~r1_tarski(D_188, '#skF_1') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_676, c_1319])).
% 3.85/1.64  tff(c_1379, plain, (![D_188]: (k1_xboole_0='#skF_4' | m1_subset_1(k7_relat_1('#skF_5', D_188), k1_zfmisc_1(k2_zfmisc_1(D_188, '#skF_4'))) | ~r1_tarski(D_188, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1357])).
% 3.85/1.64  tff(c_1381, plain, (![D_300]: (m1_subset_1(k7_relat_1('#skF_5', D_300), k1_zfmisc_1(k2_zfmisc_1(D_300, '#skF_4'))) | ~r1_tarski(D_300, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_1260, c_1379])).
% 3.85/1.64  tff(c_24, plain, (![C_29, A_26, B_27]: (v1_partfun1(C_29, A_26) | ~v1_funct_2(C_29, A_26, B_27) | ~v1_funct_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | v1_xboole_0(B_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.85/1.64  tff(c_1395, plain, (![D_300]: (v1_partfun1(k7_relat_1('#skF_5', D_300), D_300) | ~v1_funct_2(k7_relat_1('#skF_5', D_300), D_300, '#skF_4') | ~v1_funct_1(k7_relat_1('#skF_5', D_300)) | v1_xboole_0('#skF_4') | ~r1_tarski(D_300, '#skF_1'))), inference(resolution, [status(thm)], [c_1381, c_24])).
% 3.85/1.64  tff(c_1424, plain, (![D_300]: (v1_partfun1(k7_relat_1('#skF_5', D_300), D_300) | ~v1_funct_2(k7_relat_1('#skF_5', D_300), D_300, '#skF_4') | v1_xboole_0('#skF_4') | ~r1_tarski(D_300, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_679, c_1395])).
% 3.85/1.64  tff(c_1451, plain, (![D_305]: (v1_partfun1(k7_relat_1('#skF_5', D_305), D_305) | ~v1_funct_2(k7_relat_1('#skF_5', D_305), D_305, '#skF_4') | ~r1_tarski(D_305, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_1424])).
% 3.85/1.64  tff(c_1461, plain, (![C_306]: (v1_partfun1(k7_relat_1('#skF_5', C_306), C_306) | ~r1_tarski(C_306, '#skF_1'))), inference(resolution, [status(thm)], [c_1259, c_1451])).
% 3.85/1.64  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.85/1.64  tff(c_92, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.85/1.64  tff(c_95, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_92])).
% 3.85/1.64  tff(c_98, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_95])).
% 3.85/1.64  tff(c_108, plain, (![A_63, B_64, C_65, D_66]: (k7_relset_1(A_63, B_64, C_65, D_66)=k9_relat_1(C_65, D_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.85/1.64  tff(c_111, plain, (![D_66]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_66)=k9_relat_1('#skF_5', D_66))), inference(resolution, [status(thm)], [c_52, c_108])).
% 3.85/1.64  tff(c_48, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.85/1.64  tff(c_120, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_48])).
% 3.85/1.64  tff(c_8, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.85/1.64  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.64  tff(c_184, plain, (![A_88, B_89, C_90, D_91]: (k2_partfun1(A_88, B_89, C_90, D_91)=k7_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.85/1.64  tff(c_186, plain, (![D_91]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_91)=k7_relat_1('#skF_5', D_91) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_184])).
% 3.85/1.64  tff(c_189, plain, (![D_91]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_91)=k7_relat_1('#skF_5', D_91))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_186])).
% 3.85/1.64  tff(c_287, plain, (![A_104, B_105, C_106, D_107]: (m1_subset_1(k2_partfun1(A_104, B_105, C_106, D_107), k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_1(C_106))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.85/1.64  tff(c_305, plain, (![D_91]: (m1_subset_1(k7_relat_1('#skF_5', D_91), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_287])).
% 3.85/1.64  tff(c_316, plain, (![D_108]: (m1_subset_1(k7_relat_1('#skF_5', D_108), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_305])).
% 3.85/1.64  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.85/1.64  tff(c_331, plain, (![D_108]: (v1_relat_1(k7_relat_1('#skF_5', D_108)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(resolution, [status(thm)], [c_316, c_4])).
% 3.85/1.64  tff(c_348, plain, (![D_108]: (v1_relat_1(k7_relat_1('#skF_5', D_108)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_331])).
% 3.85/1.64  tff(c_202, plain, (![C_94, A_95, B_96]: (m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~r1_tarski(k2_relat_1(C_94), B_96) | ~r1_tarski(k1_relat_1(C_94), A_95) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.85/1.64  tff(c_79, plain, (![A_53, B_54, C_55, D_56]: (v1_funct_1(k2_partfun1(A_53, B_54, C_55, D_56)) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_1(C_55))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.85/1.64  tff(c_81, plain, (![D_56]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_56)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_79])).
% 3.85/1.64  tff(c_84, plain, (![D_56]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_56)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_81])).
% 3.85/1.64  tff(c_46, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.85/1.64  tff(c_61, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.85/1.64  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_61])).
% 3.85/1.64  tff(c_88, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_46])).
% 3.85/1.64  tff(c_91, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_88])).
% 3.85/1.64  tff(c_191, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_91])).
% 3.85/1.64  tff(c_226, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_202, c_191])).
% 3.85/1.64  tff(c_526, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_226])).
% 3.85/1.64  tff(c_527, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_526])).
% 3.85/1.64  tff(c_530, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_527])).
% 3.85/1.64  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_530])).
% 3.85/1.64  tff(c_535, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_526])).
% 3.85/1.64  tff(c_542, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8, c_535])).
% 3.85/1.64  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_120, c_542])).
% 3.85/1.64  tff(c_546, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_88])).
% 3.85/1.64  tff(c_547, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_88])).
% 3.85/1.64  tff(c_614, plain, (![C_174, A_175, B_176]: (v1_funct_2(C_174, A_175, B_176) | ~v1_partfun1(C_174, A_175) | ~v1_funct_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.85/1.64  tff(c_617, plain, (v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_partfun1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_547, c_614])).
% 3.85/1.64  tff(c_623, plain, (v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_partfun1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_617])).
% 3.85/1.64  tff(c_624, plain, (~v1_partfun1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_546, c_623])).
% 3.85/1.64  tff(c_677, plain, (~v1_partfun1(k7_relat_1('#skF_5', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_676, c_624])).
% 3.85/1.64  tff(c_1464, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_1461, c_677])).
% 3.85/1.64  tff(c_1468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1464])).
% 3.85/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.64  
% 3.85/1.64  Inference rules
% 3.85/1.64  ----------------------
% 3.85/1.64  #Ref     : 0
% 3.85/1.64  #Sup     : 287
% 3.85/1.64  #Fact    : 0
% 3.85/1.64  #Define  : 0
% 3.85/1.64  #Split   : 14
% 3.85/1.64  #Chain   : 0
% 3.85/1.64  #Close   : 0
% 3.85/1.64  
% 3.85/1.64  Ordering : KBO
% 3.85/1.64  
% 3.85/1.64  Simplification rules
% 3.85/1.64  ----------------------
% 3.85/1.64  #Subsume      : 33
% 3.85/1.64  #Demod        : 196
% 3.85/1.64  #Tautology    : 62
% 3.85/1.64  #SimpNegUnit  : 14
% 3.85/1.64  #BackRed      : 20
% 3.85/1.64  
% 3.85/1.64  #Partial instantiations: 0
% 3.85/1.64  #Strategies tried      : 1
% 3.85/1.64  
% 3.85/1.64  Timing (in seconds)
% 3.85/1.64  ----------------------
% 3.85/1.64  Preprocessing        : 0.34
% 3.85/1.64  Parsing              : 0.18
% 3.85/1.64  CNF conversion       : 0.02
% 3.85/1.64  Main loop            : 0.52
% 3.85/1.64  Inferencing          : 0.19
% 3.85/1.64  Reduction            : 0.17
% 3.85/1.64  Demodulation         : 0.12
% 3.85/1.64  BG Simplification    : 0.03
% 3.85/1.64  Subsumption          : 0.09
% 3.85/1.64  Abstraction          : 0.03
% 3.85/1.64  MUC search           : 0.00
% 3.85/1.64  Cooper               : 0.00
% 3.85/1.64  Total                : 0.91
% 3.85/1.64  Index Insertion      : 0.00
% 3.85/1.64  Index Deletion       : 0.00
% 3.85/1.64  Index Matching       : 0.00
% 3.85/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
