%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:52 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 201 expanded)
%              Number of leaves         :   42 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 ( 342 expanded)
%              Number of equality atoms :   59 ( 118 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_74,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1366,plain,(
    ! [A_190,B_191,C_192,D_193] :
      ( k8_relset_1(A_190,B_191,C_192,D_193) = k10_relat_1(C_192,D_193)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1369,plain,(
    ! [D_193] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_193) = k10_relat_1('#skF_3',D_193) ),
    inference(resolution,[status(thm)],[c_46,c_1366])).

tff(c_1182,plain,(
    ! [A_175,B_176,C_177] :
      ( k1_relset_1(A_175,B_176,C_177) = k1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1186,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1182])).

tff(c_68,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_68])).

tff(c_130,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_134,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_130])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_137,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_12])).

tff(c_140,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_137])).

tff(c_145,plain,(
    ! [B_64,A_65] :
      ( k2_relat_1(k7_relat_1(B_64,A_65)) = k9_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_145])).

tff(c_167,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_160])).

tff(c_688,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k7_relset_1(A_116,B_117,C_118,D_119) = k9_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_691,plain,(
    ! [D_119] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_119) = k9_relat_1('#skF_3',D_119) ),
    inference(resolution,[status(thm)],[c_46,c_688])).

tff(c_528,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_532,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_528])).

tff(c_44,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_87,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_533,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_87])).

tff(c_692,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_533])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_692])).

tff(c_696,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1187,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_696])).

tff(c_1370,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_1187])).

tff(c_723,plain,(
    ! [C_126,B_127,A_128] :
      ( v5_relat_1(C_126,B_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_727,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_723])).

tff(c_862,plain,(
    ! [C_146,A_147,B_148] :
      ( v4_relat_1(C_146,A_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_866,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_862])).

tff(c_869,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_866,c_12])).

tff(c_872,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_869])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_876,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_6])).

tff(c_880,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_876])).

tff(c_768,plain,(
    ! [B_136,A_137] :
      ( k2_relat_1(k7_relat_1(B_136,A_137)) = k9_relat_1(B_136,A_137)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1733,plain,(
    ! [B_216,A_217,A_218] :
      ( r1_tarski(k9_relat_1(B_216,A_217),A_218)
      | ~ v5_relat_1(k7_relat_1(B_216,A_217),A_218)
      | ~ v1_relat_1(k7_relat_1(B_216,A_217))
      | ~ v1_relat_1(B_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_4])).

tff(c_1739,plain,(
    ! [A_218] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_218)
      | ~ v5_relat_1('#skF_3',A_218)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_1733])).

tff(c_1759,plain,(
    ! [A_219] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_219)
      | ~ v5_relat_1('#skF_3',A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_872,c_880,c_1739])).

tff(c_18,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_821,plain,(
    ! [A_142,B_143] :
      ( k5_relat_1(k6_relat_1(A_142),B_143) = k7_relat_1(B_143,A_142)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [B_19,A_18] : k5_relat_1(k6_relat_1(B_19),k6_relat_1(A_18)) = k6_relat_1(k3_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_828,plain,(
    ! [A_18,A_142] :
      ( k7_relat_1(k6_relat_1(A_18),A_142) = k6_relat_1(k3_xboole_0(A_18,A_142))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_28])).

tff(c_837,plain,(
    ! [A_18,A_142] : k7_relat_1(k6_relat_1(A_18),A_142) = k6_relat_1(k3_xboole_0(A_18,A_142)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_828])).

tff(c_24,plain,(
    ! [A_17] : v4_relat_1(k6_relat_1(A_17),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_978,plain,(
    ! [C_153,B_154,A_155] :
      ( v4_relat_1(C_153,B_154)
      | ~ v4_relat_1(C_153,A_155)
      | ~ v1_relat_1(C_153)
      | ~ r1_tarski(A_155,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_982,plain,(
    ! [A_17,B_154] :
      ( v4_relat_1(k6_relat_1(A_17),B_154)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ r1_tarski(A_17,B_154) ) ),
    inference(resolution,[status(thm)],[c_24,c_978])).

tff(c_1002,plain,(
    ! [A_157,B_158] :
      ( v4_relat_1(k6_relat_1(A_157),B_158)
      | ~ r1_tarski(A_157,B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_982])).

tff(c_1007,plain,(
    ! [A_157,B_158] :
      ( k7_relat_1(k6_relat_1(A_157),B_158) = k6_relat_1(A_157)
      | ~ v1_relat_1(k6_relat_1(A_157))
      | ~ r1_tarski(A_157,B_158) ) ),
    inference(resolution,[status(thm)],[c_1002,c_12])).

tff(c_1041,plain,(
    ! [A_162,B_163] :
      ( k6_relat_1(k3_xboole_0(A_162,B_163)) = k6_relat_1(A_162)
      | ~ r1_tarski(A_162,B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_837,c_1007])).

tff(c_1080,plain,(
    ! [A_162,B_163] :
      ( k3_xboole_0(A_162,B_163) = k2_relat_1(k6_relat_1(A_162))
      | ~ r1_tarski(A_162,B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_18])).

tff(c_1105,plain,(
    ! [A_162,B_163] :
      ( k3_xboole_0(A_162,B_163) = A_162
      | ~ r1_tarski(A_162,B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1080])).

tff(c_1805,plain,(
    ! [A_222] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_222) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_222) ) ),
    inference(resolution,[status(thm)],[c_1759,c_1105])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k10_relat_1(B_6,k3_xboole_0(k2_relat_1(B_6),A_5)) = k10_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1856,plain,(
    ! [A_222] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_222)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1805,c_8])).

tff(c_1901,plain,(
    ! [A_223] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_223)
      | ~ v5_relat_1('#skF_3',A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1856])).

tff(c_1911,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_727,c_1901])).

tff(c_10,plain,(
    ! [A_7] :
      ( k10_relat_1(A_7,k2_relat_1(A_7)) = k1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1916,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1911,c_10])).

tff(c_1923,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1916])).

tff(c_1925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1370,c_1923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:36:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.64  
% 3.34/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.64  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.34/1.64  
% 3.34/1.64  %Foreground sorts:
% 3.34/1.64  
% 3.34/1.64  
% 3.34/1.64  %Background operators:
% 3.34/1.64  
% 3.34/1.64  
% 3.34/1.64  %Foreground operators:
% 3.34/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.34/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.34/1.64  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.34/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.34/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.34/1.64  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.34/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.34/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.34/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.34/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.34/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.34/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.34/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.34/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.64  
% 3.34/1.66  tff(f_107, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.34/1.66  tff(f_100, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.34/1.66  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.34/1.66  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.34/1.66  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.34/1.66  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.34/1.66  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.34/1.66  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.34/1.66  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.34/1.66  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.34/1.66  tff(f_62, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.34/1.66  tff(f_72, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.34/1.66  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.34/1.66  tff(f_74, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.34/1.66  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 3.34/1.66  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 3.34/1.66  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.34/1.66  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.34/1.66  tff(c_1366, plain, (![A_190, B_191, C_192, D_193]: (k8_relset_1(A_190, B_191, C_192, D_193)=k10_relat_1(C_192, D_193) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.34/1.66  tff(c_1369, plain, (![D_193]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_193)=k10_relat_1('#skF_3', D_193))), inference(resolution, [status(thm)], [c_46, c_1366])).
% 3.34/1.66  tff(c_1182, plain, (![A_175, B_176, C_177]: (k1_relset_1(A_175, B_176, C_177)=k1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.34/1.66  tff(c_1186, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1182])).
% 3.34/1.66  tff(c_68, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.34/1.66  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_68])).
% 3.34/1.66  tff(c_130, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.34/1.66  tff(c_134, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_130])).
% 3.34/1.66  tff(c_12, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.34/1.66  tff(c_137, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_134, c_12])).
% 3.34/1.66  tff(c_140, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_137])).
% 3.34/1.66  tff(c_145, plain, (![B_64, A_65]: (k2_relat_1(k7_relat_1(B_64, A_65))=k9_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.34/1.66  tff(c_160, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_145])).
% 3.34/1.66  tff(c_167, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_160])).
% 3.34/1.66  tff(c_688, plain, (![A_116, B_117, C_118, D_119]: (k7_relset_1(A_116, B_117, C_118, D_119)=k9_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.34/1.66  tff(c_691, plain, (![D_119]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_119)=k9_relat_1('#skF_3', D_119))), inference(resolution, [status(thm)], [c_46, c_688])).
% 3.34/1.66  tff(c_528, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.34/1.66  tff(c_532, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_528])).
% 3.34/1.66  tff(c_44, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.34/1.66  tff(c_87, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.34/1.66  tff(c_533, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_87])).
% 3.34/1.66  tff(c_692, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_691, c_533])).
% 3.34/1.66  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_692])).
% 3.34/1.66  tff(c_696, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.34/1.66  tff(c_1187, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_696])).
% 3.34/1.66  tff(c_1370, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1369, c_1187])).
% 3.34/1.66  tff(c_723, plain, (![C_126, B_127, A_128]: (v5_relat_1(C_126, B_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.34/1.66  tff(c_727, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_723])).
% 3.34/1.66  tff(c_862, plain, (![C_146, A_147, B_148]: (v4_relat_1(C_146, A_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.34/1.66  tff(c_866, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_862])).
% 3.34/1.66  tff(c_869, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_866, c_12])).
% 3.34/1.66  tff(c_872, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_869])).
% 3.34/1.66  tff(c_6, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.34/1.66  tff(c_876, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_872, c_6])).
% 3.34/1.66  tff(c_880, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_876])).
% 3.34/1.66  tff(c_768, plain, (![B_136, A_137]: (k2_relat_1(k7_relat_1(B_136, A_137))=k9_relat_1(B_136, A_137) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.34/1.66  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.66  tff(c_1733, plain, (![B_216, A_217, A_218]: (r1_tarski(k9_relat_1(B_216, A_217), A_218) | ~v5_relat_1(k7_relat_1(B_216, A_217), A_218) | ~v1_relat_1(k7_relat_1(B_216, A_217)) | ~v1_relat_1(B_216))), inference(superposition, [status(thm), theory('equality')], [c_768, c_4])).
% 3.34/1.66  tff(c_1739, plain, (![A_218]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_218) | ~v5_relat_1('#skF_3', A_218) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_872, c_1733])).
% 3.34/1.66  tff(c_1759, plain, (![A_219]: (r1_tarski(k2_relat_1('#skF_3'), A_219) | ~v5_relat_1('#skF_3', A_219))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_872, c_880, c_1739])).
% 3.34/1.66  tff(c_18, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.34/1.66  tff(c_22, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.34/1.66  tff(c_821, plain, (![A_142, B_143]: (k5_relat_1(k6_relat_1(A_142), B_143)=k7_relat_1(B_143, A_142) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.34/1.66  tff(c_28, plain, (![B_19, A_18]: (k5_relat_1(k6_relat_1(B_19), k6_relat_1(A_18))=k6_relat_1(k3_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.34/1.66  tff(c_828, plain, (![A_18, A_142]: (k7_relat_1(k6_relat_1(A_18), A_142)=k6_relat_1(k3_xboole_0(A_18, A_142)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_821, c_28])).
% 3.34/1.66  tff(c_837, plain, (![A_18, A_142]: (k7_relat_1(k6_relat_1(A_18), A_142)=k6_relat_1(k3_xboole_0(A_18, A_142)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_828])).
% 3.34/1.66  tff(c_24, plain, (![A_17]: (v4_relat_1(k6_relat_1(A_17), A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.34/1.66  tff(c_978, plain, (![C_153, B_154, A_155]: (v4_relat_1(C_153, B_154) | ~v4_relat_1(C_153, A_155) | ~v1_relat_1(C_153) | ~r1_tarski(A_155, B_154))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.34/1.66  tff(c_982, plain, (![A_17, B_154]: (v4_relat_1(k6_relat_1(A_17), B_154) | ~v1_relat_1(k6_relat_1(A_17)) | ~r1_tarski(A_17, B_154))), inference(resolution, [status(thm)], [c_24, c_978])).
% 3.34/1.66  tff(c_1002, plain, (![A_157, B_158]: (v4_relat_1(k6_relat_1(A_157), B_158) | ~r1_tarski(A_157, B_158))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_982])).
% 3.34/1.66  tff(c_1007, plain, (![A_157, B_158]: (k7_relat_1(k6_relat_1(A_157), B_158)=k6_relat_1(A_157) | ~v1_relat_1(k6_relat_1(A_157)) | ~r1_tarski(A_157, B_158))), inference(resolution, [status(thm)], [c_1002, c_12])).
% 3.34/1.66  tff(c_1041, plain, (![A_162, B_163]: (k6_relat_1(k3_xboole_0(A_162, B_163))=k6_relat_1(A_162) | ~r1_tarski(A_162, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_837, c_1007])).
% 3.34/1.66  tff(c_1080, plain, (![A_162, B_163]: (k3_xboole_0(A_162, B_163)=k2_relat_1(k6_relat_1(A_162)) | ~r1_tarski(A_162, B_163))), inference(superposition, [status(thm), theory('equality')], [c_1041, c_18])).
% 3.34/1.66  tff(c_1105, plain, (![A_162, B_163]: (k3_xboole_0(A_162, B_163)=A_162 | ~r1_tarski(A_162, B_163))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1080])).
% 3.34/1.66  tff(c_1805, plain, (![A_222]: (k3_xboole_0(k2_relat_1('#skF_3'), A_222)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_222))), inference(resolution, [status(thm)], [c_1759, c_1105])).
% 3.34/1.66  tff(c_8, plain, (![B_6, A_5]: (k10_relat_1(B_6, k3_xboole_0(k2_relat_1(B_6), A_5))=k10_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.66  tff(c_1856, plain, (![A_222]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_222) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_222))), inference(superposition, [status(thm), theory('equality')], [c_1805, c_8])).
% 3.34/1.66  tff(c_1901, plain, (![A_223]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_223) | ~v5_relat_1('#skF_3', A_223))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1856])).
% 3.34/1.66  tff(c_1911, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_727, c_1901])).
% 3.34/1.66  tff(c_10, plain, (![A_7]: (k10_relat_1(A_7, k2_relat_1(A_7))=k1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.66  tff(c_1916, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1911, c_10])).
% 3.34/1.66  tff(c_1923, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1916])).
% 3.34/1.66  tff(c_1925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1370, c_1923])).
% 3.34/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.66  
% 3.34/1.66  Inference rules
% 3.34/1.66  ----------------------
% 3.34/1.66  #Ref     : 0
% 3.34/1.66  #Sup     : 432
% 3.34/1.66  #Fact    : 0
% 3.34/1.66  #Define  : 0
% 3.34/1.66  #Split   : 2
% 3.34/1.66  #Chain   : 0
% 3.34/1.66  #Close   : 0
% 3.34/1.66  
% 3.34/1.66  Ordering : KBO
% 3.34/1.66  
% 3.34/1.66  Simplification rules
% 3.34/1.66  ----------------------
% 3.34/1.66  #Subsume      : 48
% 3.34/1.66  #Demod        : 264
% 3.34/1.66  #Tautology    : 216
% 3.34/1.66  #SimpNegUnit  : 1
% 3.34/1.66  #BackRed      : 6
% 3.34/1.66  
% 3.34/1.66  #Partial instantiations: 0
% 3.34/1.66  #Strategies tried      : 1
% 3.34/1.66  
% 3.34/1.66  Timing (in seconds)
% 3.34/1.66  ----------------------
% 3.34/1.66  Preprocessing        : 0.31
% 3.34/1.66  Parsing              : 0.17
% 3.34/1.66  CNF conversion       : 0.02
% 3.34/1.66  Main loop            : 0.49
% 3.34/1.66  Inferencing          : 0.19
% 3.34/1.66  Reduction            : 0.16
% 3.34/1.66  Demodulation         : 0.11
% 3.34/1.66  BG Simplification    : 0.02
% 3.34/1.66  Subsumption          : 0.07
% 3.34/1.66  Abstraction          : 0.03
% 3.34/1.66  MUC search           : 0.00
% 3.34/1.66  Cooper               : 0.00
% 3.34/1.66  Total                : 0.84
% 3.34/1.66  Index Insertion      : 0.00
% 3.34/1.66  Index Deletion       : 0.00
% 3.34/1.66  Index Matching       : 0.00
% 3.34/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
