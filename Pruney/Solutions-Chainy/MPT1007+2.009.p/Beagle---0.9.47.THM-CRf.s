%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:12 EST 2020

% Result     : Theorem 5.63s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 285 expanded)
%              Number of leaves         :   48 ( 116 expanded)
%              Depth                    :   12
%              Number of atoms          :  194 ( 678 expanded)
%              Number of equality atoms :   43 ( 159 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_37,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_86,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_146,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1('#skF_1'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_117,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_129,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_117])).

tff(c_221,plain,(
    ! [A_105] :
      ( k1_xboole_0 = A_105
      | r2_hidden(k4_tarski('#skF_2'(A_105),'#skF_3'(A_105)),A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1026,plain,(
    ! [A_200,A_201] :
      ( r2_hidden(k4_tarski('#skF_2'(A_200),'#skF_3'(A_200)),A_201)
      | ~ m1_subset_1(A_200,k1_zfmisc_1(A_201))
      | k1_xboole_0 = A_200
      | ~ v1_relat_1(A_200) ) ),
    inference(resolution,[status(thm)],[c_221,c_22])).

tff(c_18,plain,(
    ! [C_11,A_9,B_10,D_12] :
      ( C_11 = A_9
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1099,plain,(
    ! [C_203,A_204,D_205] :
      ( C_203 = '#skF_2'(A_204)
      | ~ m1_subset_1(A_204,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_203),D_205)))
      | k1_xboole_0 = A_204
      | ~ v1_relat_1(A_204) ) ),
    inference(resolution,[status(thm)],[c_1026,c_18])).

tff(c_1110,plain,
    ( '#skF_2'('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_1099])).

tff(c_1123,plain,
    ( '#skF_2'('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_1110])).

tff(c_1131,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1123])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1201,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_64])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_48,plain,(
    ! [A_32,B_35] :
      ( k1_funct_1(A_32,B_35) = k1_xboole_0
      | r2_hidden(B_35,k1_relat_1(A_32))
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_156,plain,(
    ! [C_78,B_79,A_80] :
      ( v5_relat_1(C_78,B_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_168,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_156])).

tff(c_490,plain,(
    ! [B_130,C_131,A_132] :
      ( r2_hidden(k1_funct_1(B_130,C_131),A_132)
      | ~ r2_hidden(C_131,k1_relat_1(B_130))
      | ~ v1_funct_1(B_130)
      | ~ v5_relat_1(B_130,A_132)
      | ~ v1_relat_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_505,plain,
    ( ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_490,c_62])).

tff(c_515,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_168,c_70,c_505])).

tff(c_548,plain,
    ( k1_funct_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_515])).

tff(c_554,plain,(
    k1_funct_1('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_70,c_548])).

tff(c_557,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_62])).

tff(c_1182,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_557])).

tff(c_68,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_24,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_131,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_117])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_81,plain,(
    ! [A_55] :
      ( v1_funct_1(A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_85,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_81])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_337,plain,(
    ! [A_120,B_121] :
      ( k1_funct_1(A_120,B_121) = k1_xboole_0
      | r2_hidden(B_121,k1_relat_1(A_120))
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_353,plain,(
    ! [B_121] :
      ( k1_funct_1(k1_xboole_0,B_121) = k1_xboole_0
      | r2_hidden(B_121,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_337])).

tff(c_360,plain,(
    ! [B_122] :
      ( k1_funct_1(k1_xboole_0,B_122) = k1_xboole_0
      | r2_hidden(B_122,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_85,c_353])).

tff(c_52,plain,(
    ! [B_42,A_41] :
      ( ~ r1_tarski(B_42,A_41)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_375,plain,(
    ! [B_122] :
      ( ~ r1_tarski(k1_xboole_0,B_122)
      | k1_funct_1(k1_xboole_0,B_122) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_360,c_52])).

tff(c_388,plain,(
    ! [B_122] : k1_funct_1(k1_xboole_0,B_122) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_375])).

tff(c_1185,plain,(
    ! [B_122] : k1_funct_1('#skF_6',B_122) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_1131,c_388])).

tff(c_1195,plain,(
    ! [A_19] : m1_subset_1('#skF_6',k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_24])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_604,plain,(
    ! [D_137,C_138,B_139,A_140] :
      ( r2_hidden(k1_funct_1(D_137,C_138),B_139)
      | k1_xboole_0 = B_139
      | ~ r2_hidden(C_138,A_140)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139)))
      | ~ v1_funct_2(D_137,A_140,B_139)
      | ~ v1_funct_1(D_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_628,plain,(
    ! [D_137,A_20,B_139,B_21] :
      ( r2_hidden(k1_funct_1(D_137,A_20),B_139)
      | k1_xboole_0 = B_139
      | ~ m1_subset_1(D_137,k1_zfmisc_1(k2_zfmisc_1(B_21,B_139)))
      | ~ v1_funct_2(D_137,B_21,B_139)
      | ~ v1_funct_1(D_137)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_26,c_604])).

tff(c_3644,plain,(
    ! [D_381,A_382,B_383,B_384] :
      ( r2_hidden(k1_funct_1(D_381,A_382),B_383)
      | B_383 = '#skF_6'
      | ~ m1_subset_1(D_381,k1_zfmisc_1(k2_zfmisc_1(B_384,B_383)))
      | ~ v1_funct_2(D_381,B_384,B_383)
      | ~ v1_funct_1(D_381)
      | v1_xboole_0(B_384)
      | ~ m1_subset_1(A_382,B_384) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_628])).

tff(c_3653,plain,(
    ! [A_382,B_383,B_384] :
      ( r2_hidden(k1_funct_1('#skF_6',A_382),B_383)
      | B_383 = '#skF_6'
      | ~ v1_funct_2('#skF_6',B_384,B_383)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(B_384)
      | ~ m1_subset_1(A_382,B_384) ) ),
    inference(resolution,[status(thm)],[c_1195,c_3644])).

tff(c_3671,plain,(
    ! [B_385,B_386,A_387] :
      ( r2_hidden('#skF_6',B_385)
      | B_385 = '#skF_6'
      | ~ v1_funct_2('#skF_6',B_386,B_385)
      | v1_xboole_0(B_386)
      | ~ m1_subset_1(A_387,B_386) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1185,c_3653])).

tff(c_3673,plain,(
    ! [A_387] :
      ( r2_hidden('#skF_6','#skF_5')
      | '#skF_5' = '#skF_6'
      | v1_xboole_0(k1_tarski('#skF_4'))
      | ~ m1_subset_1(A_387,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_68,c_3671])).

tff(c_3677,plain,(
    ! [A_388] : ~ m1_subset_1(A_388,k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1201,c_1182,c_3673])).

tff(c_3702,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_20,c_3677])).

tff(c_3704,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_3703,plain,(
    '#skF_2'('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_34,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | r2_hidden(k4_tarski('#skF_2'(A_28),'#skF_3'(A_28)),A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_271,plain,(
    ! [A_108,C_109,B_110] :
      ( r2_hidden(A_108,k1_relat_1(C_109))
      | ~ r2_hidden(k4_tarski(A_108,B_110),C_109)
      | ~ v1_relat_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_279,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_2'(A_28),k1_relat_1(A_28))
      | k1_xboole_0 = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(resolution,[status(thm)],[c_34,c_271])).

tff(c_3717,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3703,c_279])).

tff(c_3733,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_3717])).

tff(c_3735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3704,c_515,c_3733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.63/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.09  
% 5.66/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.09  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 5.66/2.09  
% 5.66/2.09  %Foreground sorts:
% 5.66/2.09  
% 5.66/2.09  
% 5.66/2.09  %Background operators:
% 5.66/2.09  
% 5.66/2.09  
% 5.66/2.09  %Foreground operators:
% 5.66/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.66/2.09  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.66/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.66/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.66/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.66/2.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.66/2.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.66/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.66/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.66/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.66/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.66/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.66/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.66/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.66/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.66/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.66/2.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.66/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.66/2.09  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.66/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.66/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.66/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.66/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.66/2.09  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.66/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.66/2.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.66/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.66/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.66/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.66/2.09  
% 5.74/2.11  tff(f_46, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.74/2.11  tff(f_37, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.74/2.11  tff(f_158, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 5.74/2.11  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.74/2.11  tff(f_83, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 5.74/2.11  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.74/2.11  tff(f_43, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 5.74/2.11  tff(f_108, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 5.74/2.11  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.74/2.11  tff(f_119, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 5.74/2.11  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.74/2.11  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.74/2.11  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.74/2.11  tff(f_90, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 5.74/2.11  tff(f_86, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.74/2.11  tff(f_124, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.74/2.11  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.74/2.11  tff(f_146, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.74/2.11  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 5.74/2.11  tff(c_20, plain, (![A_13]: (m1_subset_1('#skF_1'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.74/2.11  tff(c_12, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.74/2.11  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.74/2.11  tff(c_117, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.74/2.11  tff(c_129, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_117])).
% 5.74/2.11  tff(c_221, plain, (![A_105]: (k1_xboole_0=A_105 | r2_hidden(k4_tarski('#skF_2'(A_105), '#skF_3'(A_105)), A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.74/2.11  tff(c_22, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.74/2.11  tff(c_1026, plain, (![A_200, A_201]: (r2_hidden(k4_tarski('#skF_2'(A_200), '#skF_3'(A_200)), A_201) | ~m1_subset_1(A_200, k1_zfmisc_1(A_201)) | k1_xboole_0=A_200 | ~v1_relat_1(A_200))), inference(resolution, [status(thm)], [c_221, c_22])).
% 5.74/2.11  tff(c_18, plain, (![C_11, A_9, B_10, D_12]: (C_11=A_9 | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.74/2.11  tff(c_1099, plain, (![C_203, A_204, D_205]: (C_203='#skF_2'(A_204) | ~m1_subset_1(A_204, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_203), D_205))) | k1_xboole_0=A_204 | ~v1_relat_1(A_204))), inference(resolution, [status(thm)], [c_1026, c_18])).
% 5.74/2.11  tff(c_1110, plain, ('#skF_2'('#skF_6')='#skF_4' | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_1099])).
% 5.74/2.11  tff(c_1123, plain, ('#skF_2'('#skF_6')='#skF_4' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_1110])).
% 5.74/2.11  tff(c_1131, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_1123])).
% 5.74/2.11  tff(c_64, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.74/2.11  tff(c_1201, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_64])).
% 5.74/2.11  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.74/2.11  tff(c_48, plain, (![A_32, B_35]: (k1_funct_1(A_32, B_35)=k1_xboole_0 | r2_hidden(B_35, k1_relat_1(A_32)) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.74/2.11  tff(c_156, plain, (![C_78, B_79, A_80]: (v5_relat_1(C_78, B_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.74/2.11  tff(c_168, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_156])).
% 5.74/2.11  tff(c_490, plain, (![B_130, C_131, A_132]: (r2_hidden(k1_funct_1(B_130, C_131), A_132) | ~r2_hidden(C_131, k1_relat_1(B_130)) | ~v1_funct_1(B_130) | ~v5_relat_1(B_130, A_132) | ~v1_relat_1(B_130))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.74/2.11  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.74/2.11  tff(c_505, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_490, c_62])).
% 5.74/2.11  tff(c_515, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_168, c_70, c_505])).
% 5.74/2.11  tff(c_548, plain, (k1_funct_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_515])).
% 5.74/2.11  tff(c_554, plain, (k1_funct_1('#skF_6', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_129, c_70, c_548])).
% 5.74/2.11  tff(c_557, plain, (~r2_hidden(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_554, c_62])).
% 5.74/2.11  tff(c_1182, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_557])).
% 5.74/2.11  tff(c_68, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.74/2.11  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.74/2.11  tff(c_24, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.74/2.11  tff(c_131, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_117])).
% 5.74/2.11  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.74/2.11  tff(c_81, plain, (![A_55]: (v1_funct_1(A_55) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.74/2.11  tff(c_85, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_81])).
% 5.74/2.11  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.74/2.11  tff(c_337, plain, (![A_120, B_121]: (k1_funct_1(A_120, B_121)=k1_xboole_0 | r2_hidden(B_121, k1_relat_1(A_120)) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.74/2.11  tff(c_353, plain, (![B_121]: (k1_funct_1(k1_xboole_0, B_121)=k1_xboole_0 | r2_hidden(B_121, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_337])).
% 5.74/2.11  tff(c_360, plain, (![B_122]: (k1_funct_1(k1_xboole_0, B_122)=k1_xboole_0 | r2_hidden(B_122, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_85, c_353])).
% 5.74/2.11  tff(c_52, plain, (![B_42, A_41]: (~r1_tarski(B_42, A_41) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.74/2.11  tff(c_375, plain, (![B_122]: (~r1_tarski(k1_xboole_0, B_122) | k1_funct_1(k1_xboole_0, B_122)=k1_xboole_0)), inference(resolution, [status(thm)], [c_360, c_52])).
% 5.74/2.11  tff(c_388, plain, (![B_122]: (k1_funct_1(k1_xboole_0, B_122)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_375])).
% 5.74/2.11  tff(c_1185, plain, (![B_122]: (k1_funct_1('#skF_6', B_122)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_1131, c_388])).
% 5.74/2.11  tff(c_1195, plain, (![A_19]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_24])).
% 5.74/2.11  tff(c_26, plain, (![A_20, B_21]: (r2_hidden(A_20, B_21) | v1_xboole_0(B_21) | ~m1_subset_1(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.74/2.11  tff(c_604, plain, (![D_137, C_138, B_139, A_140]: (r2_hidden(k1_funct_1(D_137, C_138), B_139) | k1_xboole_0=B_139 | ~r2_hidden(C_138, A_140) | ~m1_subset_1(D_137, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))) | ~v1_funct_2(D_137, A_140, B_139) | ~v1_funct_1(D_137))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.74/2.11  tff(c_628, plain, (![D_137, A_20, B_139, B_21]: (r2_hidden(k1_funct_1(D_137, A_20), B_139) | k1_xboole_0=B_139 | ~m1_subset_1(D_137, k1_zfmisc_1(k2_zfmisc_1(B_21, B_139))) | ~v1_funct_2(D_137, B_21, B_139) | ~v1_funct_1(D_137) | v1_xboole_0(B_21) | ~m1_subset_1(A_20, B_21))), inference(resolution, [status(thm)], [c_26, c_604])).
% 5.74/2.11  tff(c_3644, plain, (![D_381, A_382, B_383, B_384]: (r2_hidden(k1_funct_1(D_381, A_382), B_383) | B_383='#skF_6' | ~m1_subset_1(D_381, k1_zfmisc_1(k2_zfmisc_1(B_384, B_383))) | ~v1_funct_2(D_381, B_384, B_383) | ~v1_funct_1(D_381) | v1_xboole_0(B_384) | ~m1_subset_1(A_382, B_384))), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_628])).
% 5.74/2.11  tff(c_3653, plain, (![A_382, B_383, B_384]: (r2_hidden(k1_funct_1('#skF_6', A_382), B_383) | B_383='#skF_6' | ~v1_funct_2('#skF_6', B_384, B_383) | ~v1_funct_1('#skF_6') | v1_xboole_0(B_384) | ~m1_subset_1(A_382, B_384))), inference(resolution, [status(thm)], [c_1195, c_3644])).
% 5.74/2.11  tff(c_3671, plain, (![B_385, B_386, A_387]: (r2_hidden('#skF_6', B_385) | B_385='#skF_6' | ~v1_funct_2('#skF_6', B_386, B_385) | v1_xboole_0(B_386) | ~m1_subset_1(A_387, B_386))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1185, c_3653])).
% 5.74/2.11  tff(c_3673, plain, (![A_387]: (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | v1_xboole_0(k1_tarski('#skF_4')) | ~m1_subset_1(A_387, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_68, c_3671])).
% 5.74/2.11  tff(c_3677, plain, (![A_388]: (~m1_subset_1(A_388, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_12, c_1201, c_1182, c_3673])).
% 5.74/2.11  tff(c_3702, plain, $false, inference(resolution, [status(thm)], [c_20, c_3677])).
% 5.74/2.11  tff(c_3704, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_1123])).
% 5.74/2.11  tff(c_3703, plain, ('#skF_2'('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1123])).
% 5.74/2.11  tff(c_34, plain, (![A_28]: (k1_xboole_0=A_28 | r2_hidden(k4_tarski('#skF_2'(A_28), '#skF_3'(A_28)), A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.74/2.11  tff(c_271, plain, (![A_108, C_109, B_110]: (r2_hidden(A_108, k1_relat_1(C_109)) | ~r2_hidden(k4_tarski(A_108, B_110), C_109) | ~v1_relat_1(C_109))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.74/2.11  tff(c_279, plain, (![A_28]: (r2_hidden('#skF_2'(A_28), k1_relat_1(A_28)) | k1_xboole_0=A_28 | ~v1_relat_1(A_28))), inference(resolution, [status(thm)], [c_34, c_271])).
% 5.74/2.11  tff(c_3717, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3703, c_279])).
% 5.74/2.11  tff(c_3733, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_3717])).
% 5.74/2.11  tff(c_3735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3704, c_515, c_3733])).
% 5.74/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.11  
% 5.74/2.11  Inference rules
% 5.74/2.11  ----------------------
% 5.74/2.11  #Ref     : 0
% 5.74/2.11  #Sup     : 756
% 5.74/2.11  #Fact    : 0
% 5.74/2.11  #Define  : 0
% 5.74/2.11  #Split   : 9
% 5.74/2.11  #Chain   : 0
% 5.74/2.11  #Close   : 0
% 5.74/2.11  
% 5.74/2.11  Ordering : KBO
% 5.74/2.11  
% 5.74/2.11  Simplification rules
% 5.74/2.11  ----------------------
% 5.74/2.11  #Subsume      : 154
% 5.74/2.11  #Demod        : 561
% 5.74/2.11  #Tautology    : 183
% 5.74/2.11  #SimpNegUnit  : 30
% 5.74/2.11  #BackRed      : 48
% 5.74/2.11  
% 5.74/2.11  #Partial instantiations: 0
% 5.74/2.11  #Strategies tried      : 1
% 5.74/2.11  
% 5.74/2.11  Timing (in seconds)
% 5.74/2.11  ----------------------
% 5.74/2.11  Preprocessing        : 0.35
% 5.74/2.11  Parsing              : 0.19
% 5.74/2.11  CNF conversion       : 0.02
% 5.79/2.11  Main loop            : 0.93
% 5.79/2.11  Inferencing          : 0.30
% 5.79/2.11  Reduction            : 0.32
% 5.79/2.11  Demodulation         : 0.22
% 5.79/2.11  BG Simplification    : 0.04
% 5.79/2.12  Subsumption          : 0.19
% 5.79/2.12  Abstraction          : 0.04
% 5.79/2.12  MUC search           : 0.00
% 5.79/2.12  Cooper               : 0.00
% 5.79/2.12  Total                : 1.32
% 5.79/2.12  Index Insertion      : 0.00
% 5.79/2.12  Index Deletion       : 0.00
% 5.79/2.12  Index Matching       : 0.00
% 5.79/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
