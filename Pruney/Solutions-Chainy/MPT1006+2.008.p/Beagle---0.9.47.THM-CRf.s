%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:03 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 246 expanded)
%              Number of leaves         :   50 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 ( 419 expanded)
%              Number of equality atoms :   53 ( 145 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_113,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_84,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_32,plain,(
    ! [B_38] : k2_zfmisc_1(k1_xboole_0,B_38) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_65,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_60])).

tff(c_30,plain,(
    ! [A_37] : k2_zfmisc_1(A_37,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_208,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_269,plain,(
    ! [C_102] :
      ( v1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_208])).

tff(c_277,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_65,c_269])).

tff(c_56,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_1'(A_58),A_58)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_389,plain,(
    ! [C_109,B_110,A_111] :
      ( ~ v1_xboole_0(C_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(C_109))
      | ~ r2_hidden(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_391,plain,(
    ! [A_111] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_111,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_389])).

tff(c_398,plain,(
    ! [A_112] : ~ r2_hidden(A_112,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_391])).

tff(c_403,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_56,c_398])).

tff(c_34,plain,(
    ! [A_39] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_217,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_208])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_375,plain,(
    ! [A_108] :
      ( k10_relat_1(A_108,k2_relat_1(A_108)) = k1_relat_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_384,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_375])).

tff(c_388,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_48,c_384])).

tff(c_443,plain,(
    k10_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_403,c_403,c_388])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_172,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k4_xboole_0(B_94,A_93)) = k2_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_181,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_172])).

tff(c_185,plain,(
    ! [A_95] : k2_xboole_0(A_95,k1_xboole_0) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_181])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_191,plain,(
    ! [A_95] : k2_xboole_0(k1_xboole_0,A_95) = A_95 ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_2])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_280,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k3_xboole_0(A_103,B_104)) = k4_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_289,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_280])).

tff(c_293,plain,(
    ! [A_105] : k4_xboole_0(A_105,k1_xboole_0) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_289])).

tff(c_14,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_299,plain,(
    ! [A_105] : k5_xboole_0(k1_xboole_0,A_105) = k2_xboole_0(k1_xboole_0,A_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_14])).

tff(c_316,plain,(
    ! [A_106] : k5_xboole_0(k1_xboole_0,A_106) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_299])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_323,plain,(
    ! [B_4] : k4_xboole_0(k1_xboole_0,B_4) = k3_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_6])).

tff(c_348,plain,(
    ! [B_4] : k3_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_323])).

tff(c_404,plain,(
    ! [B_4] : k3_xboole_0('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_403,c_348])).

tff(c_422,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_403,c_46])).

tff(c_680,plain,(
    ! [B_134,A_135] :
      ( k10_relat_1(B_134,k3_xboole_0(k2_relat_1(B_134),A_135)) = k10_relat_1(B_134,A_135)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_693,plain,(
    ! [A_135] :
      ( k10_relat_1('#skF_4',k3_xboole_0('#skF_4',A_135)) = k10_relat_1('#skF_4',A_135)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_680])).

tff(c_698,plain,(
    ! [A_135] : k10_relat_1('#skF_4',A_135) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_443,c_404,c_693])).

tff(c_419,plain,(
    ! [A_39] : m1_subset_1('#skF_4',k1_zfmisc_1(A_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_34])).

tff(c_758,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( k8_relset_1(A_144,B_145,C_146,D_147) = k10_relat_1(C_146,D_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_765,plain,(
    ! [A_144,B_145,D_147] : k8_relset_1(A_144,B_145,'#skF_4',D_147) = k10_relat_1('#skF_4',D_147) ),
    inference(resolution,[status(thm)],[c_419,c_758])).

tff(c_767,plain,(
    ! [A_144,B_145,D_147] : k8_relset_1(A_144,B_145,'#skF_4',D_147) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_765])).

tff(c_58,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_416,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_403,c_58])).

tff(c_772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:13:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.54  
% 2.78/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.54  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.78/1.54  
% 2.78/1.54  %Foreground sorts:
% 2.78/1.54  
% 2.78/1.54  
% 2.78/1.54  %Background operators:
% 2.78/1.54  
% 2.78/1.54  
% 2.78/1.54  %Foreground operators:
% 2.78/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.54  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.78/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.78/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.78/1.54  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.78/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.54  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.78/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.78/1.54  
% 2.97/1.56  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.97/1.56  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.97/1.56  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.97/1.56  tff(f_113, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.97/1.56  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.97/1.56  tff(f_73, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.97/1.56  tff(f_58, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.97/1.56  tff(f_84, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.97/1.56  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.97/1.56  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.97/1.56  tff(f_36, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.97/1.56  tff(f_38, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.97/1.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.97/1.56  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.97/1.56  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.97/1.56  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.97/1.56  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.97/1.56  tff(c_32, plain, (![B_38]: (k2_zfmisc_1(k1_xboole_0, B_38)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.97/1.56  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.97/1.56  tff(c_65, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_60])).
% 2.97/1.56  tff(c_30, plain, (![A_37]: (k2_zfmisc_1(A_37, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.97/1.56  tff(c_208, plain, (![C_96, A_97, B_98]: (v1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.56  tff(c_269, plain, (![C_102]: (v1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_208])).
% 2.97/1.56  tff(c_277, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_65, c_269])).
% 2.97/1.56  tff(c_56, plain, (![A_58]: (r2_hidden('#skF_1'(A_58), A_58) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.97/1.56  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.97/1.56  tff(c_389, plain, (![C_109, B_110, A_111]: (~v1_xboole_0(C_109) | ~m1_subset_1(B_110, k1_zfmisc_1(C_109)) | ~r2_hidden(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.97/1.56  tff(c_391, plain, (![A_111]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_111, '#skF_4'))), inference(resolution, [status(thm)], [c_65, c_389])).
% 2.97/1.56  tff(c_398, plain, (![A_112]: (~r2_hidden(A_112, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_391])).
% 2.97/1.56  tff(c_403, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_56, c_398])).
% 2.97/1.56  tff(c_34, plain, (![A_39]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.97/1.56  tff(c_217, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_208])).
% 2.97/1.56  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.97/1.56  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.97/1.56  tff(c_375, plain, (![A_108]: (k10_relat_1(A_108, k2_relat_1(A_108))=k1_relat_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.97/1.56  tff(c_384, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_375])).
% 2.97/1.56  tff(c_388, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_217, c_48, c_384])).
% 2.97/1.56  tff(c_443, plain, (k10_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_403, c_403, c_403, c_388])).
% 2.97/1.56  tff(c_10, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.97/1.56  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.97/1.56  tff(c_172, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k4_xboole_0(B_94, A_93))=k2_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.97/1.56  tff(c_181, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_172])).
% 2.97/1.56  tff(c_185, plain, (![A_95]: (k2_xboole_0(A_95, k1_xboole_0)=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_181])).
% 2.97/1.56  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.97/1.56  tff(c_191, plain, (![A_95]: (k2_xboole_0(k1_xboole_0, A_95)=A_95)), inference(superposition, [status(thm), theory('equality')], [c_185, c_2])).
% 2.97/1.56  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.97/1.56  tff(c_280, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k3_xboole_0(A_103, B_104))=k4_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.97/1.56  tff(c_289, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_280])).
% 2.97/1.56  tff(c_293, plain, (![A_105]: (k4_xboole_0(A_105, k1_xboole_0)=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_289])).
% 2.97/1.56  tff(c_14, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.97/1.56  tff(c_299, plain, (![A_105]: (k5_xboole_0(k1_xboole_0, A_105)=k2_xboole_0(k1_xboole_0, A_105))), inference(superposition, [status(thm), theory('equality')], [c_293, c_14])).
% 2.97/1.56  tff(c_316, plain, (![A_106]: (k5_xboole_0(k1_xboole_0, A_106)=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_191, c_299])).
% 2.97/1.56  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.97/1.56  tff(c_323, plain, (![B_4]: (k4_xboole_0(k1_xboole_0, B_4)=k3_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_316, c_6])).
% 2.97/1.56  tff(c_348, plain, (![B_4]: (k3_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_323])).
% 2.97/1.56  tff(c_404, plain, (![B_4]: (k3_xboole_0('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_403, c_348])).
% 2.97/1.56  tff(c_422, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_403, c_403, c_46])).
% 2.97/1.56  tff(c_680, plain, (![B_134, A_135]: (k10_relat_1(B_134, k3_xboole_0(k2_relat_1(B_134), A_135))=k10_relat_1(B_134, A_135) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.97/1.56  tff(c_693, plain, (![A_135]: (k10_relat_1('#skF_4', k3_xboole_0('#skF_4', A_135))=k10_relat_1('#skF_4', A_135) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_422, c_680])).
% 2.97/1.56  tff(c_698, plain, (![A_135]: (k10_relat_1('#skF_4', A_135)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_443, c_404, c_693])).
% 2.97/1.56  tff(c_419, plain, (![A_39]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_39)))), inference(demodulation, [status(thm), theory('equality')], [c_403, c_34])).
% 2.97/1.56  tff(c_758, plain, (![A_144, B_145, C_146, D_147]: (k8_relset_1(A_144, B_145, C_146, D_147)=k10_relat_1(C_146, D_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.97/1.56  tff(c_765, plain, (![A_144, B_145, D_147]: (k8_relset_1(A_144, B_145, '#skF_4', D_147)=k10_relat_1('#skF_4', D_147))), inference(resolution, [status(thm)], [c_419, c_758])).
% 2.97/1.56  tff(c_767, plain, (![A_144, B_145, D_147]: (k8_relset_1(A_144, B_145, '#skF_4', D_147)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_698, c_765])).
% 2.97/1.56  tff(c_58, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.97/1.56  tff(c_416, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_403, c_403, c_58])).
% 2.97/1.56  tff(c_772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_767, c_416])).
% 2.97/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.56  
% 2.97/1.56  Inference rules
% 2.97/1.56  ----------------------
% 2.97/1.56  #Ref     : 0
% 2.97/1.56  #Sup     : 160
% 2.97/1.56  #Fact    : 0
% 2.97/1.56  #Define  : 0
% 2.97/1.56  #Split   : 0
% 2.97/1.56  #Chain   : 0
% 2.97/1.56  #Close   : 0
% 2.97/1.56  
% 2.97/1.56  Ordering : KBO
% 2.97/1.56  
% 2.97/1.56  Simplification rules
% 2.97/1.56  ----------------------
% 2.97/1.56  #Subsume      : 5
% 2.97/1.56  #Demod        : 102
% 2.97/1.56  #Tautology    : 141
% 2.97/1.56  #SimpNegUnit  : 0
% 2.97/1.56  #BackRed      : 22
% 2.97/1.56  
% 2.97/1.56  #Partial instantiations: 0
% 2.97/1.56  #Strategies tried      : 1
% 2.97/1.56  
% 2.97/1.56  Timing (in seconds)
% 2.97/1.56  ----------------------
% 2.97/1.56  Preprocessing        : 0.44
% 2.97/1.56  Parsing              : 0.26
% 2.97/1.56  CNF conversion       : 0.02
% 2.97/1.56  Main loop            : 0.26
% 2.97/1.56  Inferencing          : 0.10
% 2.97/1.56  Reduction            : 0.09
% 2.97/1.56  Demodulation         : 0.07
% 2.97/1.56  BG Simplification    : 0.02
% 2.97/1.56  Subsumption          : 0.03
% 2.97/1.56  Abstraction          : 0.02
% 2.97/1.57  MUC search           : 0.00
% 2.97/1.57  Cooper               : 0.00
% 2.97/1.57  Total                : 0.74
% 2.97/1.57  Index Insertion      : 0.00
% 2.97/1.57  Index Deletion       : 0.00
% 2.97/1.57  Index Matching       : 0.00
% 2.97/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
