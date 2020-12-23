%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:51 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 146 expanded)
%              Number of leaves         :   42 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  140 ( 237 expanded)
%              Number of equality atoms :   56 (  90 expanded)
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

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
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

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_95,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_77,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1597,plain,(
    ! [A_220,B_221,C_222,D_223] :
      ( k8_relset_1(A_220,B_221,C_222,D_223) = k10_relat_1(C_222,D_223)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1600,plain,(
    ! [D_223] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_223) = k10_relat_1('#skF_3',D_223) ),
    inference(resolution,[status(thm)],[c_46,c_1597])).

tff(c_1114,plain,(
    ! [A_179,B_180,C_181] :
      ( k1_relset_1(A_179,B_180,C_181) = k1_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1118,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1114])).

tff(c_68,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_68])).

tff(c_207,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_211,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_207])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_214,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_14])).

tff(c_217,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_214])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_221,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_6])).

tff(c_225,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_221])).

tff(c_622,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k7_relset_1(A_118,B_119,C_120,D_121) = k9_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_625,plain,(
    ! [D_121] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_121) = k9_relat_1('#skF_3',D_121) ),
    inference(resolution,[status(thm)],[c_46,c_622])).

tff(c_385,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_389,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_385])).

tff(c_44,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_87,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_390,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_87])).

tff(c_626,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_390])).

tff(c_629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_626])).

tff(c_630,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1119,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1118,c_630])).

tff(c_1601,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1600,c_1119])).

tff(c_641,plain,(
    ! [C_123,B_124,A_125] :
      ( v5_relat_1(C_123,B_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_645,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_641])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [B_20,A_19] : k5_relat_1(k6_relat_1(B_20),k6_relat_1(A_19)) = k6_relat_1(k3_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_910,plain,(
    ! [B_167,A_168] :
      ( k9_relat_1(B_167,k2_relat_1(A_168)) = k2_relat_1(k5_relat_1(A_168,B_167))
      | ~ v1_relat_1(B_167)
      | ~ v1_relat_1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_938,plain,(
    ! [A_17,B_167] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_17),B_167)) = k9_relat_1(B_167,A_17)
      | ~ v1_relat_1(B_167)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_910])).

tff(c_951,plain,(
    ! [A_169,B_170] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_169),B_170)) = k9_relat_1(B_170,A_169)
      | ~ v1_relat_1(B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_938])).

tff(c_978,plain,(
    ! [A_19,B_20] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_19,B_20))) = k9_relat_1(k6_relat_1(A_19),B_20)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_951])).

tff(c_982,plain,(
    ! [A_19,B_20] : k9_relat_1(k6_relat_1(A_19),B_20) = k3_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_978])).

tff(c_24,plain,(
    ! [A_18] : v4_relat_1(k6_relat_1(A_18),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_757,plain,(
    ! [C_145,B_146,A_147] :
      ( v4_relat_1(C_145,B_146)
      | ~ v4_relat_1(C_145,A_147)
      | ~ v1_relat_1(C_145)
      | ~ r1_tarski(A_147,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_761,plain,(
    ! [A_18,B_146] :
      ( v4_relat_1(k6_relat_1(A_18),B_146)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ r1_tarski(A_18,B_146) ) ),
    inference(resolution,[status(thm)],[c_24,c_757])).

tff(c_809,plain,(
    ! [A_152,B_153] :
      ( v4_relat_1(k6_relat_1(A_152),B_153)
      | ~ r1_tarski(A_152,B_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_761])).

tff(c_814,plain,(
    ! [A_152,B_153] :
      ( k7_relat_1(k6_relat_1(A_152),B_153) = k6_relat_1(A_152)
      | ~ v1_relat_1(k6_relat_1(A_152))
      | ~ r1_tarski(A_152,B_153) ) ),
    inference(resolution,[status(thm)],[c_809,c_14])).

tff(c_821,plain,(
    ! [A_154,B_155] :
      ( k7_relat_1(k6_relat_1(A_154),B_155) = k6_relat_1(A_154)
      | ~ r1_tarski(A_154,B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_814])).

tff(c_827,plain,(
    ! [A_154,B_155] :
      ( k9_relat_1(k6_relat_1(A_154),B_155) = k2_relat_1(k6_relat_1(A_154))
      | ~ v1_relat_1(k6_relat_1(A_154))
      | ~ r1_tarski(A_154,B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_6])).

tff(c_840,plain,(
    ! [A_154,B_155] :
      ( k9_relat_1(k6_relat_1(A_154),B_155) = A_154
      | ~ r1_tarski(A_154,B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_827])).

tff(c_1040,plain,(
    ! [A_176,B_177] :
      ( k3_xboole_0(A_176,B_177) = A_176
      | ~ r1_tarski(A_176,B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_840])).

tff(c_1245,plain,(
    ! [B_195,A_196] :
      ( k3_xboole_0(k2_relat_1(B_195),A_196) = k2_relat_1(B_195)
      | ~ v5_relat_1(B_195,A_196)
      | ~ v1_relat_1(B_195) ) ),
    inference(resolution,[status(thm)],[c_4,c_1040])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k10_relat_1(B_9,k3_xboole_0(k2_relat_1(B_9),A_8)) = k10_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1914,plain,(
    ! [B_255,A_256] :
      ( k10_relat_1(B_255,k2_relat_1(B_255)) = k10_relat_1(B_255,A_256)
      | ~ v1_relat_1(B_255)
      | ~ v5_relat_1(B_255,A_256)
      | ~ v1_relat_1(B_255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1245,c_10])).

tff(c_1928,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_645,c_1914])).

tff(c_1945,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1928])).

tff(c_12,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1952,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1945,c_12])).

tff(c_1959,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1952])).

tff(c_1961,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1601,c_1959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:11:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.62  
% 3.50/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.62  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.50/1.62  
% 3.50/1.62  %Foreground sorts:
% 3.50/1.62  
% 3.50/1.62  
% 3.50/1.62  %Background operators:
% 3.50/1.62  
% 3.50/1.62  
% 3.50/1.62  %Foreground operators:
% 3.50/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.50/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.50/1.62  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.50/1.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.50/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.50/1.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.50/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.50/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.50/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.50/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.50/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.62  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.50/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.50/1.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.50/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.50/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.50/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.50/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.62  
% 3.90/1.64  tff(f_110, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.90/1.64  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.90/1.64  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.90/1.64  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.90/1.64  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.90/1.64  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.90/1.64  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.90/1.64  tff(f_99, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.90/1.64  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.90/1.64  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.90/1.64  tff(f_75, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.90/1.64  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.90/1.64  tff(f_77, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.90/1.64  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.90/1.64  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 3.90/1.64  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 3.90/1.64  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.90/1.64  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.64  tff(c_1597, plain, (![A_220, B_221, C_222, D_223]: (k8_relset_1(A_220, B_221, C_222, D_223)=k10_relat_1(C_222, D_223) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.90/1.64  tff(c_1600, plain, (![D_223]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_223)=k10_relat_1('#skF_3', D_223))), inference(resolution, [status(thm)], [c_46, c_1597])).
% 3.90/1.64  tff(c_1114, plain, (![A_179, B_180, C_181]: (k1_relset_1(A_179, B_180, C_181)=k1_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.90/1.64  tff(c_1118, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1114])).
% 3.90/1.64  tff(c_68, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.90/1.64  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_68])).
% 3.90/1.64  tff(c_207, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.90/1.64  tff(c_211, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_207])).
% 3.90/1.64  tff(c_14, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.90/1.64  tff(c_214, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_211, c_14])).
% 3.90/1.64  tff(c_217, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_214])).
% 3.90/1.64  tff(c_6, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.90/1.64  tff(c_221, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_217, c_6])).
% 3.90/1.64  tff(c_225, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_221])).
% 3.90/1.64  tff(c_622, plain, (![A_118, B_119, C_120, D_121]: (k7_relset_1(A_118, B_119, C_120, D_121)=k9_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.90/1.64  tff(c_625, plain, (![D_121]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_121)=k9_relat_1('#skF_3', D_121))), inference(resolution, [status(thm)], [c_46, c_622])).
% 3.90/1.64  tff(c_385, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.90/1.64  tff(c_389, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_385])).
% 3.90/1.64  tff(c_44, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.64  tff(c_87, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.90/1.64  tff(c_390, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_389, c_87])).
% 3.90/1.64  tff(c_626, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_625, c_390])).
% 3.90/1.64  tff(c_629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_626])).
% 3.90/1.64  tff(c_630, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.90/1.64  tff(c_1119, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1118, c_630])).
% 3.90/1.64  tff(c_1601, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1600, c_1119])).
% 3.90/1.64  tff(c_641, plain, (![C_123, B_124, A_125]: (v5_relat_1(C_123, B_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.90/1.64  tff(c_645, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_641])).
% 3.90/1.64  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.64  tff(c_22, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.90/1.64  tff(c_20, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.90/1.64  tff(c_28, plain, (![B_20, A_19]: (k5_relat_1(k6_relat_1(B_20), k6_relat_1(A_19))=k6_relat_1(k3_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.90/1.64  tff(c_910, plain, (![B_167, A_168]: (k9_relat_1(B_167, k2_relat_1(A_168))=k2_relat_1(k5_relat_1(A_168, B_167)) | ~v1_relat_1(B_167) | ~v1_relat_1(A_168))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.90/1.64  tff(c_938, plain, (![A_17, B_167]: (k2_relat_1(k5_relat_1(k6_relat_1(A_17), B_167))=k9_relat_1(B_167, A_17) | ~v1_relat_1(B_167) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_910])).
% 3.90/1.64  tff(c_951, plain, (![A_169, B_170]: (k2_relat_1(k5_relat_1(k6_relat_1(A_169), B_170))=k9_relat_1(B_170, A_169) | ~v1_relat_1(B_170))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_938])).
% 3.90/1.64  tff(c_978, plain, (![A_19, B_20]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_19, B_20)))=k9_relat_1(k6_relat_1(A_19), B_20) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_951])).
% 3.90/1.64  tff(c_982, plain, (![A_19, B_20]: (k9_relat_1(k6_relat_1(A_19), B_20)=k3_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_978])).
% 3.90/1.64  tff(c_24, plain, (![A_18]: (v4_relat_1(k6_relat_1(A_18), A_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.90/1.64  tff(c_757, plain, (![C_145, B_146, A_147]: (v4_relat_1(C_145, B_146) | ~v4_relat_1(C_145, A_147) | ~v1_relat_1(C_145) | ~r1_tarski(A_147, B_146))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.90/1.64  tff(c_761, plain, (![A_18, B_146]: (v4_relat_1(k6_relat_1(A_18), B_146) | ~v1_relat_1(k6_relat_1(A_18)) | ~r1_tarski(A_18, B_146))), inference(resolution, [status(thm)], [c_24, c_757])).
% 3.90/1.64  tff(c_809, plain, (![A_152, B_153]: (v4_relat_1(k6_relat_1(A_152), B_153) | ~r1_tarski(A_152, B_153))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_761])).
% 3.90/1.64  tff(c_814, plain, (![A_152, B_153]: (k7_relat_1(k6_relat_1(A_152), B_153)=k6_relat_1(A_152) | ~v1_relat_1(k6_relat_1(A_152)) | ~r1_tarski(A_152, B_153))), inference(resolution, [status(thm)], [c_809, c_14])).
% 3.90/1.64  tff(c_821, plain, (![A_154, B_155]: (k7_relat_1(k6_relat_1(A_154), B_155)=k6_relat_1(A_154) | ~r1_tarski(A_154, B_155))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_814])).
% 3.90/1.64  tff(c_827, plain, (![A_154, B_155]: (k9_relat_1(k6_relat_1(A_154), B_155)=k2_relat_1(k6_relat_1(A_154)) | ~v1_relat_1(k6_relat_1(A_154)) | ~r1_tarski(A_154, B_155))), inference(superposition, [status(thm), theory('equality')], [c_821, c_6])).
% 3.90/1.64  tff(c_840, plain, (![A_154, B_155]: (k9_relat_1(k6_relat_1(A_154), B_155)=A_154 | ~r1_tarski(A_154, B_155))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_827])).
% 3.90/1.64  tff(c_1040, plain, (![A_176, B_177]: (k3_xboole_0(A_176, B_177)=A_176 | ~r1_tarski(A_176, B_177))), inference(demodulation, [status(thm), theory('equality')], [c_982, c_840])).
% 3.90/1.64  tff(c_1245, plain, (![B_195, A_196]: (k3_xboole_0(k2_relat_1(B_195), A_196)=k2_relat_1(B_195) | ~v5_relat_1(B_195, A_196) | ~v1_relat_1(B_195))), inference(resolution, [status(thm)], [c_4, c_1040])).
% 3.90/1.64  tff(c_10, plain, (![B_9, A_8]: (k10_relat_1(B_9, k3_xboole_0(k2_relat_1(B_9), A_8))=k10_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.90/1.64  tff(c_1914, plain, (![B_255, A_256]: (k10_relat_1(B_255, k2_relat_1(B_255))=k10_relat_1(B_255, A_256) | ~v1_relat_1(B_255) | ~v5_relat_1(B_255, A_256) | ~v1_relat_1(B_255))), inference(superposition, [status(thm), theory('equality')], [c_1245, c_10])).
% 3.90/1.64  tff(c_1928, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_645, c_1914])).
% 3.90/1.64  tff(c_1945, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1928])).
% 3.90/1.64  tff(c_12, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.90/1.64  tff(c_1952, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1945, c_12])).
% 3.90/1.64  tff(c_1959, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1952])).
% 3.90/1.64  tff(c_1961, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1601, c_1959])).
% 3.90/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.64  
% 3.90/1.64  Inference rules
% 3.90/1.64  ----------------------
% 3.90/1.64  #Ref     : 0
% 3.90/1.64  #Sup     : 433
% 3.90/1.64  #Fact    : 0
% 3.90/1.64  #Define  : 0
% 3.90/1.64  #Split   : 2
% 3.90/1.64  #Chain   : 0
% 3.90/1.64  #Close   : 0
% 3.90/1.64  
% 3.90/1.64  Ordering : KBO
% 3.90/1.64  
% 3.90/1.64  Simplification rules
% 3.90/1.64  ----------------------
% 3.90/1.64  #Subsume      : 43
% 3.90/1.64  #Demod        : 327
% 3.90/1.64  #Tautology    : 177
% 3.90/1.64  #SimpNegUnit  : 1
% 3.90/1.64  #BackRed      : 7
% 3.90/1.64  
% 3.90/1.64  #Partial instantiations: 0
% 3.90/1.64  #Strategies tried      : 1
% 3.90/1.64  
% 3.90/1.64  Timing (in seconds)
% 3.90/1.64  ----------------------
% 3.90/1.64  Preprocessing        : 0.33
% 3.90/1.64  Parsing              : 0.18
% 3.90/1.64  CNF conversion       : 0.02
% 3.90/1.64  Main loop            : 0.55
% 3.90/1.64  Inferencing          : 0.21
% 3.90/1.64  Reduction            : 0.18
% 3.90/1.64  Demodulation         : 0.13
% 3.90/1.64  BG Simplification    : 0.03
% 3.90/1.64  Subsumption          : 0.09
% 3.90/1.64  Abstraction          : 0.03
% 3.90/1.64  MUC search           : 0.00
% 3.90/1.64  Cooper               : 0.00
% 3.90/1.64  Total                : 0.91
% 3.90/1.64  Index Insertion      : 0.00
% 3.90/1.64  Index Deletion       : 0.00
% 3.90/1.64  Index Matching       : 0.00
% 3.90/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
