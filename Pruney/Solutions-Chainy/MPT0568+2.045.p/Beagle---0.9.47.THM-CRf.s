%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:26 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 143 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 196 expanded)
%              Number of equality atoms :   21 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_9 > #skF_11 > #skF_4 > #skF_6 > #skF_3 > #skF_8 > #skF_5 > #skF_10 > #skF_7 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_110,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_113,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_38,plain,(
    ! [A_27] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_102,plain,(
    ! [A_112,B_113] : k4_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = k3_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_129,plain,(
    ! [B_114] : k3_xboole_0(k1_xboole_0,B_114) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_64,plain,(
    ! [A_73] :
      ( r2_hidden('#skF_9'(A_73),A_73)
      | v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_95,plain,(
    ! [A_107,B_108,C_109] :
      ( ~ r1_xboole_0(A_107,B_108)
      | ~ r2_hidden(C_109,k3_xboole_0(A_107,B_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,(
    ! [A_107,B_108] :
      ( ~ r1_xboole_0(A_107,B_108)
      | v1_relat_1(k3_xboole_0(A_107,B_108)) ) ),
    inference(resolution,[status(thm)],[c_64,c_95])).

tff(c_134,plain,(
    ! [B_114] :
      ( ~ r1_xboole_0(k1_xboole_0,B_114)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_100])).

tff(c_148,plain,(
    ! [B_114] : ~ r1_xboole_0(k1_xboole_0,B_114) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_112,plain,(
    ! [B_113] : k3_xboole_0(k1_xboole_0,B_113) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_168,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_1'(A_124,B_125),k3_xboole_0(A_124,B_125))
      | r1_xboole_0(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_174,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_113),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_168])).

tff(c_176,plain,(
    ! [B_113] : r2_hidden('#skF_1'(k1_xboole_0,B_113),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_174])).

tff(c_191,plain,(
    ! [C_131,A_132,B_133] :
      ( r2_hidden(C_131,A_132)
      | ~ r2_hidden(C_131,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_193,plain,(
    ! [B_113,A_132] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_113),A_132)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_132)) ) ),
    inference(resolution,[status(thm)],[c_176,c_191])).

tff(c_207,plain,(
    ! [B_134,A_135] : r2_hidden('#skF_1'(k1_xboole_0,B_134),A_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_193])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_224,plain,(
    ! [A_1,B_2] : ~ r1_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_207,c_4])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(k1_tarski(A_17),B_18)
      | r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_228,plain,(
    ! [A_17,B_18] : r2_hidden(A_17,B_18) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_24])).

tff(c_12,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_242,plain,(
    ! [C_140,A_141] : C_140 = A_141 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_12])).

tff(c_66,plain,(
    k10_relat_1(k1_xboole_0,'#skF_12') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1452,plain,(
    ! [C_140] : k1_xboole_0 != C_140 ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_66])).

tff(c_1624,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1452])).

tff(c_1625,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_2586,plain,(
    ! [A_1172,B_1173,C_1174] :
      ( r2_hidden(k4_tarski('#skF_5'(A_1172,B_1173,C_1174),'#skF_6'(A_1172,B_1173,C_1174)),A_1172)
      | r2_hidden('#skF_7'(A_1172,B_1173,C_1174),C_1174)
      | k10_relat_1(A_1172,B_1173) = C_1174
      | ~ v1_relat_1(A_1172) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_137,plain,(
    ! [B_114,C_5] :
      ( ~ r1_xboole_0(k1_xboole_0,B_114)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_4])).

tff(c_1637,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_2626,plain,(
    ! [B_1173,C_1174] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_1173,C_1174),C_1174)
      | k10_relat_1(k1_xboole_0,B_1173) = C_1174
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2586,c_1637])).

tff(c_2654,plain,(
    ! [B_1175,C_1176] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_1175,C_1176),C_1176)
      | k10_relat_1(k1_xboole_0,B_1175) = C_1176 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_2626])).

tff(c_2713,plain,(
    ! [B_1175] : k10_relat_1(k1_xboole_0,B_1175) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2654,c_1637])).

tff(c_2737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_66])).

tff(c_2738,plain,(
    ! [B_114] : ~ r1_xboole_0(k1_xboole_0,B_114) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_2772,plain,(
    ! [A_1191,B_1192] :
      ( r2_hidden('#skF_1'(A_1191,B_1192),k3_xboole_0(A_1191,B_1192))
      | r1_xboole_0(A_1191,B_1192) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2780,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_113),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2772])).

tff(c_2784,plain,(
    ! [B_1193] : r2_hidden('#skF_1'(k1_xboole_0,B_1193),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_2738,c_2780])).

tff(c_32,plain,(
    ! [C_24,A_21,B_22] :
      ( r2_hidden(C_24,A_21)
      | ~ r2_hidden(C_24,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2788,plain,(
    ! [B_1193,A_21] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_1193),A_21)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_2784,c_32])).

tff(c_2799,plain,(
    ! [B_1196,A_1197] : r2_hidden('#skF_1'(k1_xboole_0,B_1196),A_1197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2788])).

tff(c_2822,plain,(
    ! [A_1,B_2] : ~ r1_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2799,c_4])).

tff(c_2826,plain,(
    ! [A_17,B_18] : r2_hidden(A_17,B_18) ),
    inference(negUnitSimplification,[status(thm)],[c_2822,c_24])).

tff(c_2843,plain,(
    ! [C_1202,A_1203] : C_1202 = A_1203 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2826,c_12])).

tff(c_4439,plain,(
    ! [C_1202] : k1_xboole_0 != C_1202 ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_66])).

tff(c_4611,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:31:12 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.68  
% 3.82/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_9 > #skF_11 > #skF_4 > #skF_6 > #skF_3 > #skF_8 > #skF_5 > #skF_10 > #skF_7 > #skF_2 > #skF_1 > #skF_12
% 3.82/1.68  
% 3.82/1.68  %Foreground sorts:
% 3.82/1.68  
% 3.82/1.68  
% 3.82/1.68  %Background operators:
% 3.82/1.68  
% 3.82/1.68  
% 3.82/1.68  %Foreground operators:
% 3.82/1.68  tff('#skF_9', type, '#skF_9': $i > $i).
% 3.82/1.68  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 3.82/1.68  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.68  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.82/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.82/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.82/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.82/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.82/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.68  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.82/1.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.82/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.82/1.68  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 3.82/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.82/1.68  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.82/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.82/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.82/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.82/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.82/1.68  tff('#skF_12', type, '#skF_12': $i).
% 3.82/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.82/1.68  
% 4.15/1.69  tff(f_81, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.15/1.69  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.15/1.69  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.15/1.69  tff(f_110, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 4.15/1.69  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.15/1.69  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.15/1.69  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.15/1.69  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.15/1.69  tff(f_113, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 4.15/1.69  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 4.15/1.69  tff(c_38, plain, (![A_27]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.15/1.69  tff(c_102, plain, (![A_112, B_113]: (k4_xboole_0(A_112, k4_xboole_0(A_112, B_113))=k3_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.15/1.69  tff(c_8, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.15/1.69  tff(c_129, plain, (![B_114]: (k3_xboole_0(k1_xboole_0, B_114)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 4.15/1.69  tff(c_64, plain, (![A_73]: (r2_hidden('#skF_9'(A_73), A_73) | v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.15/1.69  tff(c_95, plain, (![A_107, B_108, C_109]: (~r1_xboole_0(A_107, B_108) | ~r2_hidden(C_109, k3_xboole_0(A_107, B_108)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.15/1.69  tff(c_100, plain, (![A_107, B_108]: (~r1_xboole_0(A_107, B_108) | v1_relat_1(k3_xboole_0(A_107, B_108)))), inference(resolution, [status(thm)], [c_64, c_95])).
% 4.15/1.69  tff(c_134, plain, (![B_114]: (~r1_xboole_0(k1_xboole_0, B_114) | v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_129, c_100])).
% 4.15/1.69  tff(c_148, plain, (![B_114]: (~r1_xboole_0(k1_xboole_0, B_114))), inference(splitLeft, [status(thm)], [c_134])).
% 4.15/1.69  tff(c_112, plain, (![B_113]: (k3_xboole_0(k1_xboole_0, B_113)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 4.15/1.69  tff(c_168, plain, (![A_124, B_125]: (r2_hidden('#skF_1'(A_124, B_125), k3_xboole_0(A_124, B_125)) | r1_xboole_0(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.15/1.69  tff(c_174, plain, (![B_113]: (r2_hidden('#skF_1'(k1_xboole_0, B_113), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_113))), inference(superposition, [status(thm), theory('equality')], [c_112, c_168])).
% 4.15/1.69  tff(c_176, plain, (![B_113]: (r2_hidden('#skF_1'(k1_xboole_0, B_113), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_174])).
% 4.15/1.69  tff(c_191, plain, (![C_131, A_132, B_133]: (r2_hidden(C_131, A_132) | ~r2_hidden(C_131, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.15/1.69  tff(c_193, plain, (![B_113, A_132]: (r2_hidden('#skF_1'(k1_xboole_0, B_113), A_132) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_132)))), inference(resolution, [status(thm)], [c_176, c_191])).
% 4.15/1.69  tff(c_207, plain, (![B_134, A_135]: (r2_hidden('#skF_1'(k1_xboole_0, B_134), A_135))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_193])).
% 4.15/1.69  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.15/1.69  tff(c_224, plain, (![A_1, B_2]: (~r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_207, c_4])).
% 4.15/1.69  tff(c_24, plain, (![A_17, B_18]: (r1_xboole_0(k1_tarski(A_17), B_18) | r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.15/1.69  tff(c_228, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18))), inference(negUnitSimplification, [status(thm)], [c_224, c_24])).
% 4.15/1.69  tff(c_12, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.15/1.69  tff(c_242, plain, (![C_140, A_141]: (C_140=A_141)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_12])).
% 4.15/1.69  tff(c_66, plain, (k10_relat_1(k1_xboole_0, '#skF_12')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.15/1.69  tff(c_1452, plain, (![C_140]: (k1_xboole_0!=C_140)), inference(superposition, [status(thm), theory('equality')], [c_242, c_66])).
% 4.15/1.69  tff(c_1624, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_1452])).
% 4.15/1.69  tff(c_1625, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_134])).
% 4.15/1.69  tff(c_2586, plain, (![A_1172, B_1173, C_1174]: (r2_hidden(k4_tarski('#skF_5'(A_1172, B_1173, C_1174), '#skF_6'(A_1172, B_1173, C_1174)), A_1172) | r2_hidden('#skF_7'(A_1172, B_1173, C_1174), C_1174) | k10_relat_1(A_1172, B_1173)=C_1174 | ~v1_relat_1(A_1172))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.15/1.69  tff(c_137, plain, (![B_114, C_5]: (~r1_xboole_0(k1_xboole_0, B_114) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_129, c_4])).
% 4.15/1.69  tff(c_1637, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_137])).
% 4.15/1.69  tff(c_2626, plain, (![B_1173, C_1174]: (r2_hidden('#skF_7'(k1_xboole_0, B_1173, C_1174), C_1174) | k10_relat_1(k1_xboole_0, B_1173)=C_1174 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2586, c_1637])).
% 4.15/1.69  tff(c_2654, plain, (![B_1175, C_1176]: (r2_hidden('#skF_7'(k1_xboole_0, B_1175, C_1176), C_1176) | k10_relat_1(k1_xboole_0, B_1175)=C_1176)), inference(demodulation, [status(thm), theory('equality')], [c_1625, c_2626])).
% 4.15/1.69  tff(c_2713, plain, (![B_1175]: (k10_relat_1(k1_xboole_0, B_1175)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2654, c_1637])).
% 4.15/1.69  tff(c_2737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2713, c_66])).
% 4.15/1.69  tff(c_2738, plain, (![B_114]: (~r1_xboole_0(k1_xboole_0, B_114))), inference(splitRight, [status(thm)], [c_137])).
% 4.15/1.69  tff(c_2772, plain, (![A_1191, B_1192]: (r2_hidden('#skF_1'(A_1191, B_1192), k3_xboole_0(A_1191, B_1192)) | r1_xboole_0(A_1191, B_1192))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.15/1.69  tff(c_2780, plain, (![B_113]: (r2_hidden('#skF_1'(k1_xboole_0, B_113), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_113))), inference(superposition, [status(thm), theory('equality')], [c_112, c_2772])).
% 4.15/1.69  tff(c_2784, plain, (![B_1193]: (r2_hidden('#skF_1'(k1_xboole_0, B_1193), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_2738, c_2780])).
% 4.15/1.69  tff(c_32, plain, (![C_24, A_21, B_22]: (r2_hidden(C_24, A_21) | ~r2_hidden(C_24, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.15/1.69  tff(c_2788, plain, (![B_1193, A_21]: (r2_hidden('#skF_1'(k1_xboole_0, B_1193), A_21) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_2784, c_32])).
% 4.15/1.69  tff(c_2799, plain, (![B_1196, A_1197]: (r2_hidden('#skF_1'(k1_xboole_0, B_1196), A_1197))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2788])).
% 4.15/1.69  tff(c_2822, plain, (![A_1, B_2]: (~r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2799, c_4])).
% 4.15/1.69  tff(c_2826, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18))), inference(negUnitSimplification, [status(thm)], [c_2822, c_24])).
% 4.15/1.69  tff(c_2843, plain, (![C_1202, A_1203]: (C_1202=A_1203)), inference(demodulation, [status(thm), theory('equality')], [c_2826, c_12])).
% 4.15/1.69  tff(c_4439, plain, (![C_1202]: (k1_xboole_0!=C_1202)), inference(superposition, [status(thm), theory('equality')], [c_2843, c_66])).
% 4.15/1.69  tff(c_4611, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_4439])).
% 4.15/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.69  
% 4.15/1.69  Inference rules
% 4.15/1.69  ----------------------
% 4.15/1.69  #Ref     : 3
% 4.15/1.69  #Sup     : 993
% 4.15/1.69  #Fact    : 0
% 4.15/1.69  #Define  : 0
% 4.15/1.70  #Split   : 4
% 4.15/1.70  #Chain   : 0
% 4.15/1.70  #Close   : 0
% 4.15/1.70  
% 4.15/1.70  Ordering : KBO
% 4.15/1.70  
% 4.15/1.70  Simplification rules
% 4.15/1.70  ----------------------
% 4.15/1.70  #Subsume      : 53
% 4.15/1.70  #Demod        : 114
% 4.15/1.70  #Tautology    : 97
% 4.15/1.70  #SimpNegUnit  : 10
% 4.15/1.70  #BackRed      : 26
% 4.15/1.70  
% 4.15/1.70  #Partial instantiations: 988
% 4.15/1.70  #Strategies tried      : 1
% 4.15/1.70  
% 4.15/1.70  Timing (in seconds)
% 4.15/1.70  ----------------------
% 4.15/1.70  Preprocessing        : 0.31
% 4.15/1.70  Parsing              : 0.17
% 4.15/1.70  CNF conversion       : 0.03
% 4.15/1.70  Main loop            : 0.63
% 4.15/1.70  Inferencing          : 0.25
% 4.15/1.70  Reduction            : 0.18
% 4.15/1.70  Demodulation         : 0.12
% 4.15/1.70  BG Simplification    : 0.03
% 4.15/1.70  Subsumption          : 0.11
% 4.15/1.70  Abstraction          : 0.03
% 4.15/1.70  MUC search           : 0.00
% 4.15/1.70  Cooper               : 0.00
% 4.15/1.70  Total                : 0.97
% 4.15/1.70  Index Insertion      : 0.00
% 4.15/1.70  Index Deletion       : 0.00
% 4.15/1.70  Index Matching       : 0.00
% 4.15/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
