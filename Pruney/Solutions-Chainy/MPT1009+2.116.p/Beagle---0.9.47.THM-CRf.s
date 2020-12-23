%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:58 EST 2020

% Result     : Theorem 22.34s
% Output     : CNFRefutation 22.34s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 745 expanded)
%              Number of leaves         :   43 ( 281 expanded)
%              Depth                    :   15
%              Number of atoms          :  213 (1862 expanded)
%              Number of equality atoms :   89 ( 800 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_54,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_255,plain,(
    ! [B_84,A_85] :
      ( v1_relat_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_261,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_255])).

tff(c_268,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_261])).

tff(c_56,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k9_relat_1(B_28,A_27),k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_36,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_162,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_174,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_36,c_162])).

tff(c_16,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39205,plain,(
    ! [A_843,B_844,C_845,D_846] :
      ( k7_relset_1(A_843,B_844,C_845,D_846) = k9_relat_1(C_845,D_846)
      | ~ m1_subset_1(C_845,k1_zfmisc_1(k2_zfmisc_1(A_843,B_844))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_39219,plain,(
    ! [D_846] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_846) = k9_relat_1('#skF_4',D_846) ),
    inference(resolution,[status(thm)],[c_76,c_39205])).

tff(c_711,plain,(
    ! [B_157,A_158] :
      ( k1_tarski(k1_funct_1(B_157,A_158)) = k2_relat_1(B_157)
      | k1_tarski(A_158) != k1_relat_1(B_157)
      | ~ v1_funct_1(B_157)
      | ~ v1_relat_1(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_72,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_726,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_72])).

tff(c_738,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_80,c_726])).

tff(c_39346,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39219,c_738])).

tff(c_39347,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_39346])).

tff(c_392,plain,(
    ! [C_115,A_116,B_117] :
      ( v4_relat_1(C_115,A_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_411,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_392])).

tff(c_48,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(B_22),A_21)
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39380,plain,(
    ! [A_874,B_875,C_876,D_877] :
      ( k1_enumset1(A_874,B_875,C_876) = D_877
      | k2_tarski(A_874,C_876) = D_877
      | k2_tarski(B_875,C_876) = D_877
      | k2_tarski(A_874,B_875) = D_877
      | k1_tarski(C_876) = D_877
      | k1_tarski(B_875) = D_877
      | k1_tarski(A_874) = D_877
      | k1_xboole_0 = D_877
      | ~ r1_tarski(D_877,k1_enumset1(A_874,B_875,C_876)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_39413,plain,(
    ! [A_4,B_5,D_877] :
      ( k1_enumset1(A_4,A_4,B_5) = D_877
      | k2_tarski(A_4,B_5) = D_877
      | k2_tarski(A_4,B_5) = D_877
      | k2_tarski(A_4,A_4) = D_877
      | k1_tarski(B_5) = D_877
      | k1_tarski(A_4) = D_877
      | k1_tarski(A_4) = D_877
      | k1_xboole_0 = D_877
      | ~ r1_tarski(D_877,k2_tarski(A_4,B_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_39380])).

tff(c_45305,plain,(
    ! [A_1151,B_1152,D_1153] :
      ( k2_tarski(A_1151,B_1152) = D_1153
      | k2_tarski(A_1151,B_1152) = D_1153
      | k2_tarski(A_1151,B_1152) = D_1153
      | k1_tarski(A_1151) = D_1153
      | k1_tarski(B_1152) = D_1153
      | k1_tarski(A_1151) = D_1153
      | k1_tarski(A_1151) = D_1153
      | k1_xboole_0 = D_1153
      | ~ r1_tarski(D_1153,k2_tarski(A_1151,B_1152)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_39413])).

tff(c_45329,plain,(
    ! [A_3,D_1153] :
      ( k2_tarski(A_3,A_3) = D_1153
      | k2_tarski(A_3,A_3) = D_1153
      | k2_tarski(A_3,A_3) = D_1153
      | k1_tarski(A_3) = D_1153
      | k1_tarski(A_3) = D_1153
      | k1_tarski(A_3) = D_1153
      | k1_tarski(A_3) = D_1153
      | k1_xboole_0 = D_1153
      | ~ r1_tarski(D_1153,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_45305])).

tff(c_74816,plain,(
    ! [A_1499,D_1500] :
      ( k1_tarski(A_1499) = D_1500
      | k1_tarski(A_1499) = D_1500
      | k1_tarski(A_1499) = D_1500
      | k1_tarski(A_1499) = D_1500
      | k1_tarski(A_1499) = D_1500
      | k1_tarski(A_1499) = D_1500
      | k1_tarski(A_1499) = D_1500
      | k1_xboole_0 = D_1500
      | ~ r1_tarski(D_1500,k1_tarski(A_1499)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_8,c_45329])).

tff(c_75001,plain,(
    ! [A_1503,B_1504] :
      ( k1_tarski(A_1503) = k1_relat_1(B_1504)
      | k1_relat_1(B_1504) = k1_xboole_0
      | ~ v4_relat_1(B_1504,k1_tarski(A_1503))
      | ~ v1_relat_1(B_1504) ) ),
    inference(resolution,[status(thm)],[c_48,c_74816])).

tff(c_75103,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_411,c_75001])).

tff(c_75144,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_75103])).

tff(c_75145,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_39347,c_75144])).

tff(c_39285,plain,(
    ! [B_863,A_864] :
      ( m1_subset_1(B_863,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_863),A_864)))
      | ~ r1_tarski(k2_relat_1(B_863),A_864)
      | ~ v1_funct_1(B_863)
      | ~ v1_relat_1(B_863) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_38,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_41073,plain,(
    ! [B_997,A_998] :
      ( r1_tarski(B_997,k2_zfmisc_1(k1_relat_1(B_997),A_998))
      | ~ r1_tarski(k2_relat_1(B_997),A_998)
      | ~ v1_funct_1(B_997)
      | ~ v1_relat_1(B_997) ) ),
    inference(resolution,[status(thm)],[c_39285,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41116,plain,(
    ! [B_997,A_998] :
      ( k2_zfmisc_1(k1_relat_1(B_997),A_998) = B_997
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(B_997),A_998),B_997)
      | ~ r1_tarski(k2_relat_1(B_997),A_998)
      | ~ v1_funct_1(B_997)
      | ~ v1_relat_1(B_997) ) ),
    inference(resolution,[status(thm)],[c_41073,c_2])).

tff(c_75229,plain,(
    ! [A_998] :
      ( k2_zfmisc_1(k1_relat_1('#skF_4'),A_998) = '#skF_4'
      | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,A_998),'#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_998)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75145,c_41116])).

tff(c_75483,plain,(
    ! [A_998] :
      ( k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_998) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_80,c_174,c_16,c_16,c_75145,c_75229])).

tff(c_75824,plain,(
    ! [A_1510] : ~ r1_tarski(k2_relat_1('#skF_4'),A_1510) ),
    inference(splitLeft,[status(thm)],[c_75483])).

tff(c_75890,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_75824])).

tff(c_75891,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_75483])).

tff(c_76097,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75891,c_174])).

tff(c_107,plain,(
    ! [A_44,B_45] : v1_relat_1(k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_109,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_107])).

tff(c_14,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_523,plain,(
    ! [C_130,B_131,A_132] :
      ( v5_relat_1(C_130,B_131)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_583,plain,(
    ! [A_145,B_146,A_147] :
      ( v5_relat_1(A_145,B_146)
      | ~ r1_tarski(A_145,k2_zfmisc_1(A_147,B_146)) ) ),
    inference(resolution,[status(thm)],[c_40,c_523])).

tff(c_615,plain,(
    ! [A_147,B_146] : v5_relat_1(k2_zfmisc_1(A_147,B_146),B_146) ),
    inference(resolution,[status(thm)],[c_6,c_583])).

tff(c_457,plain,(
    ! [B_121,A_122] :
      ( r1_tarski(k2_relat_1(B_121),A_122)
      | ~ v5_relat_1(B_121,A_122)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_208,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(B_81,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_232,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_174,c_208])).

tff(c_626,plain,(
    ! [B_151] :
      ( k2_relat_1(B_151) = k1_xboole_0
      | ~ v5_relat_1(B_151,k1_xboole_0)
      | ~ v1_relat_1(B_151) ) ),
    inference(resolution,[status(thm)],[c_457,c_232])).

tff(c_630,plain,(
    ! [A_147] :
      ( k2_relat_1(k2_zfmisc_1(A_147,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_147,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_615,c_626])).

tff(c_641,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_14,c_14,c_630])).

tff(c_658,plain,(
    ! [A_27] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_27),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_56])).

tff(c_671,plain,(
    ! [A_152] : r1_tarski(k9_relat_1(k1_xboole_0,A_152),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_658])).

tff(c_683,plain,(
    ! [A_152] : k9_relat_1(k1_xboole_0,A_152) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_671,c_232])).

tff(c_76083,plain,(
    ! [A_152] : k9_relat_1('#skF_4',A_152) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75891,c_75891,c_683])).

tff(c_39254,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39219,c_72])).

tff(c_76728,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76083,c_39254])).

tff(c_76732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76097,c_76728])).

tff(c_76733,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_39346])).

tff(c_76865,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_76733])).

tff(c_76869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_76865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:58:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.34/13.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.34/13.09  
% 22.34/13.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.34/13.09  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 22.34/13.09  
% 22.34/13.09  %Foreground sorts:
% 22.34/13.09  
% 22.34/13.09  
% 22.34/13.09  %Background operators:
% 22.34/13.09  
% 22.34/13.09  
% 22.34/13.09  %Foreground operators:
% 22.34/13.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.34/13.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.34/13.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.34/13.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.34/13.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.34/13.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.34/13.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 22.34/13.09  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 22.34/13.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.34/13.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.34/13.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.34/13.09  tff('#skF_2', type, '#skF_2': $i).
% 22.34/13.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 22.34/13.09  tff('#skF_3', type, '#skF_3': $i).
% 22.34/13.09  tff('#skF_1', type, '#skF_1': $i).
% 22.34/13.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 22.34/13.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.34/13.09  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 22.34/13.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.34/13.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.34/13.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.34/13.09  tff('#skF_4', type, '#skF_4': $i).
% 22.34/13.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.34/13.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 22.34/13.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.34/13.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.34/13.09  
% 22.34/13.11  tff(f_101, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 22.34/13.11  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 22.34/13.11  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 22.34/13.11  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 22.34/13.11  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.34/13.11  tff(f_70, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 22.34/13.11  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 22.34/13.11  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 22.34/13.11  tff(f_123, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 22.34/13.11  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 22.34/13.11  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 22.34/13.11  tff(f_93, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 22.34/13.11  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 22.34/13.11  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 22.34/13.11  tff(f_68, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 22.34/13.11  tff(f_135, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 22.34/13.11  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 22.34/13.11  tff(c_54, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 22.34/13.11  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 22.34/13.11  tff(c_255, plain, (![B_84, A_85]: (v1_relat_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_87])).
% 22.34/13.11  tff(c_261, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_255])).
% 22.34/13.11  tff(c_268, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_261])).
% 22.34/13.11  tff(c_56, plain, (![B_28, A_27]: (r1_tarski(k9_relat_1(B_28, A_27), k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_105])).
% 22.34/13.11  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.34/13.11  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 22.34/13.11  tff(c_36, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 22.34/13.11  tff(c_162, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~m1_subset_1(A_70, k1_zfmisc_1(B_71)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.34/13.11  tff(c_174, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_36, c_162])).
% 22.34/13.11  tff(c_16, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.34/13.11  tff(c_39205, plain, (![A_843, B_844, C_845, D_846]: (k7_relset_1(A_843, B_844, C_845, D_846)=k9_relat_1(C_845, D_846) | ~m1_subset_1(C_845, k1_zfmisc_1(k2_zfmisc_1(A_843, B_844))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 22.34/13.11  tff(c_39219, plain, (![D_846]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_846)=k9_relat_1('#skF_4', D_846))), inference(resolution, [status(thm)], [c_76, c_39205])).
% 22.34/13.11  tff(c_711, plain, (![B_157, A_158]: (k1_tarski(k1_funct_1(B_157, A_158))=k2_relat_1(B_157) | k1_tarski(A_158)!=k1_relat_1(B_157) | ~v1_funct_1(B_157) | ~v1_relat_1(B_157))), inference(cnfTransformation, [status(thm)], [f_113])).
% 22.34/13.11  tff(c_72, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 22.34/13.11  tff(c_726, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_711, c_72])).
% 22.34/13.11  tff(c_738, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_80, c_726])).
% 22.34/13.11  tff(c_39346, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39219, c_738])).
% 22.34/13.11  tff(c_39347, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_39346])).
% 22.34/13.11  tff(c_392, plain, (![C_115, A_116, B_117]: (v4_relat_1(C_115, A_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 22.34/13.11  tff(c_411, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_76, c_392])).
% 22.34/13.11  tff(c_48, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(B_22), A_21) | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 22.34/13.11  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.34/13.11  tff(c_10, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.34/13.11  tff(c_39380, plain, (![A_874, B_875, C_876, D_877]: (k1_enumset1(A_874, B_875, C_876)=D_877 | k2_tarski(A_874, C_876)=D_877 | k2_tarski(B_875, C_876)=D_877 | k2_tarski(A_874, B_875)=D_877 | k1_tarski(C_876)=D_877 | k1_tarski(B_875)=D_877 | k1_tarski(A_874)=D_877 | k1_xboole_0=D_877 | ~r1_tarski(D_877, k1_enumset1(A_874, B_875, C_876)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 22.34/13.11  tff(c_39413, plain, (![A_4, B_5, D_877]: (k1_enumset1(A_4, A_4, B_5)=D_877 | k2_tarski(A_4, B_5)=D_877 | k2_tarski(A_4, B_5)=D_877 | k2_tarski(A_4, A_4)=D_877 | k1_tarski(B_5)=D_877 | k1_tarski(A_4)=D_877 | k1_tarski(A_4)=D_877 | k1_xboole_0=D_877 | ~r1_tarski(D_877, k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_39380])).
% 22.34/13.11  tff(c_45305, plain, (![A_1151, B_1152, D_1153]: (k2_tarski(A_1151, B_1152)=D_1153 | k2_tarski(A_1151, B_1152)=D_1153 | k2_tarski(A_1151, B_1152)=D_1153 | k1_tarski(A_1151)=D_1153 | k1_tarski(B_1152)=D_1153 | k1_tarski(A_1151)=D_1153 | k1_tarski(A_1151)=D_1153 | k1_xboole_0=D_1153 | ~r1_tarski(D_1153, k2_tarski(A_1151, B_1152)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_39413])).
% 22.34/13.11  tff(c_45329, plain, (![A_3, D_1153]: (k2_tarski(A_3, A_3)=D_1153 | k2_tarski(A_3, A_3)=D_1153 | k2_tarski(A_3, A_3)=D_1153 | k1_tarski(A_3)=D_1153 | k1_tarski(A_3)=D_1153 | k1_tarski(A_3)=D_1153 | k1_tarski(A_3)=D_1153 | k1_xboole_0=D_1153 | ~r1_tarski(D_1153, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_45305])).
% 22.34/13.11  tff(c_74816, plain, (![A_1499, D_1500]: (k1_tarski(A_1499)=D_1500 | k1_tarski(A_1499)=D_1500 | k1_tarski(A_1499)=D_1500 | k1_tarski(A_1499)=D_1500 | k1_tarski(A_1499)=D_1500 | k1_tarski(A_1499)=D_1500 | k1_tarski(A_1499)=D_1500 | k1_xboole_0=D_1500 | ~r1_tarski(D_1500, k1_tarski(A_1499)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_8, c_45329])).
% 22.34/13.11  tff(c_75001, plain, (![A_1503, B_1504]: (k1_tarski(A_1503)=k1_relat_1(B_1504) | k1_relat_1(B_1504)=k1_xboole_0 | ~v4_relat_1(B_1504, k1_tarski(A_1503)) | ~v1_relat_1(B_1504))), inference(resolution, [status(thm)], [c_48, c_74816])).
% 22.34/13.11  tff(c_75103, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_411, c_75001])).
% 22.34/13.11  tff(c_75144, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_268, c_75103])).
% 22.34/13.11  tff(c_75145, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_39347, c_75144])).
% 22.34/13.11  tff(c_39285, plain, (![B_863, A_864]: (m1_subset_1(B_863, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_863), A_864))) | ~r1_tarski(k2_relat_1(B_863), A_864) | ~v1_funct_1(B_863) | ~v1_relat_1(B_863))), inference(cnfTransformation, [status(thm)], [f_135])).
% 22.34/13.11  tff(c_38, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.34/13.11  tff(c_41073, plain, (![B_997, A_998]: (r1_tarski(B_997, k2_zfmisc_1(k1_relat_1(B_997), A_998)) | ~r1_tarski(k2_relat_1(B_997), A_998) | ~v1_funct_1(B_997) | ~v1_relat_1(B_997))), inference(resolution, [status(thm)], [c_39285, c_38])).
% 22.34/13.11  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.34/13.11  tff(c_41116, plain, (![B_997, A_998]: (k2_zfmisc_1(k1_relat_1(B_997), A_998)=B_997 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(B_997), A_998), B_997) | ~r1_tarski(k2_relat_1(B_997), A_998) | ~v1_funct_1(B_997) | ~v1_relat_1(B_997))), inference(resolution, [status(thm)], [c_41073, c_2])).
% 22.34/13.11  tff(c_75229, plain, (![A_998]: (k2_zfmisc_1(k1_relat_1('#skF_4'), A_998)='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_xboole_0, A_998), '#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), A_998) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75145, c_41116])).
% 22.34/13.11  tff(c_75483, plain, (![A_998]: (k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_4'), A_998))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_80, c_174, c_16, c_16, c_75145, c_75229])).
% 22.34/13.11  tff(c_75824, plain, (![A_1510]: (~r1_tarski(k2_relat_1('#skF_4'), A_1510))), inference(splitLeft, [status(thm)], [c_75483])).
% 22.34/13.11  tff(c_75890, plain, $false, inference(resolution, [status(thm)], [c_6, c_75824])).
% 22.34/13.11  tff(c_75891, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_75483])).
% 22.34/13.11  tff(c_76097, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_75891, c_174])).
% 22.34/13.11  tff(c_107, plain, (![A_44, B_45]: (v1_relat_1(k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 22.34/13.11  tff(c_109, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_107])).
% 22.34/13.11  tff(c_14, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.34/13.11  tff(c_40, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.34/13.11  tff(c_523, plain, (![C_130, B_131, A_132]: (v5_relat_1(C_130, B_131) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 22.34/13.11  tff(c_583, plain, (![A_145, B_146, A_147]: (v5_relat_1(A_145, B_146) | ~r1_tarski(A_145, k2_zfmisc_1(A_147, B_146)))), inference(resolution, [status(thm)], [c_40, c_523])).
% 22.34/13.11  tff(c_615, plain, (![A_147, B_146]: (v5_relat_1(k2_zfmisc_1(A_147, B_146), B_146))), inference(resolution, [status(thm)], [c_6, c_583])).
% 22.34/13.11  tff(c_457, plain, (![B_121, A_122]: (r1_tarski(k2_relat_1(B_121), A_122) | ~v5_relat_1(B_121, A_122) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.34/13.11  tff(c_208, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(B_81, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.34/13.11  tff(c_232, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_174, c_208])).
% 22.34/13.11  tff(c_626, plain, (![B_151]: (k2_relat_1(B_151)=k1_xboole_0 | ~v5_relat_1(B_151, k1_xboole_0) | ~v1_relat_1(B_151))), inference(resolution, [status(thm)], [c_457, c_232])).
% 22.34/13.11  tff(c_630, plain, (![A_147]: (k2_relat_1(k2_zfmisc_1(A_147, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_147, k1_xboole_0)))), inference(resolution, [status(thm)], [c_615, c_626])).
% 22.34/13.11  tff(c_641, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_109, c_14, c_14, c_630])).
% 22.34/13.11  tff(c_658, plain, (![A_27]: (r1_tarski(k9_relat_1(k1_xboole_0, A_27), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_641, c_56])).
% 22.34/13.11  tff(c_671, plain, (![A_152]: (r1_tarski(k9_relat_1(k1_xboole_0, A_152), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_658])).
% 22.34/13.11  tff(c_683, plain, (![A_152]: (k9_relat_1(k1_xboole_0, A_152)=k1_xboole_0)), inference(resolution, [status(thm)], [c_671, c_232])).
% 22.34/13.11  tff(c_76083, plain, (![A_152]: (k9_relat_1('#skF_4', A_152)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75891, c_75891, c_683])).
% 22.34/13.11  tff(c_39254, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_39219, c_72])).
% 22.34/13.11  tff(c_76728, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76083, c_39254])).
% 22.34/13.11  tff(c_76732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76097, c_76728])).
% 22.34/13.11  tff(c_76733, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_39346])).
% 22.34/13.11  tff(c_76865, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_76733])).
% 22.34/13.11  tff(c_76869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_76865])).
% 22.34/13.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.34/13.11  
% 22.34/13.11  Inference rules
% 22.34/13.11  ----------------------
% 22.34/13.11  #Ref     : 0
% 22.34/13.11  #Sup     : 17042
% 22.34/13.11  #Fact    : 0
% 22.34/13.11  #Define  : 0
% 22.34/13.11  #Split   : 27
% 22.34/13.11  #Chain   : 0
% 22.34/13.11  #Close   : 0
% 22.34/13.11  
% 22.34/13.11  Ordering : KBO
% 22.34/13.11  
% 22.34/13.11  Simplification rules
% 22.34/13.11  ----------------------
% 22.34/13.11  #Subsume      : 4813
% 22.34/13.11  #Demod        : 23746
% 22.34/13.11  #Tautology    : 6104
% 22.34/13.11  #SimpNegUnit  : 457
% 22.34/13.11  #BackRed      : 497
% 22.34/13.11  
% 22.34/13.11  #Partial instantiations: 0
% 22.34/13.11  #Strategies tried      : 1
% 22.34/13.11  
% 22.34/13.11  Timing (in seconds)
% 22.34/13.11  ----------------------
% 22.34/13.11  Preprocessing        : 0.35
% 22.34/13.11  Parsing              : 0.18
% 22.34/13.11  CNF conversion       : 0.02
% 22.34/13.12  Main loop            : 11.93
% 22.34/13.12  Inferencing          : 1.90
% 22.34/13.12  Reduction            : 4.29
% 22.34/13.12  Demodulation         : 3.39
% 22.34/13.12  BG Simplification    : 0.29
% 22.34/13.12  Subsumption          : 4.99
% 22.34/13.12  Abstraction          : 0.47
% 22.34/13.12  MUC search           : 0.00
% 22.34/13.12  Cooper               : 0.00
% 22.34/13.12  Total                : 12.32
% 22.34/13.12  Index Insertion      : 0.00
% 22.34/13.12  Index Deletion       : 0.00
% 22.34/13.12  Index Matching       : 0.00
% 22.34/13.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
