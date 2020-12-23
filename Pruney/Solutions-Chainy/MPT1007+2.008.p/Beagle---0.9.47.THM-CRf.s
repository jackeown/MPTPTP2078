%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:12 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 266 expanded)
%              Number of leaves         :   50 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 ( 626 expanded)
%              Number of equality atoms :   43 ( 147 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
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

tff(f_103,axiom,(
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

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_114,axiom,(
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

tff(f_81,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_61,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_80,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_69,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_123,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_131,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_123])).

tff(c_197,plain,(
    ! [A_99] :
      ( k1_xboole_0 = A_99
      | r2_hidden(k4_tarski('#skF_2'(A_99),'#skF_3'(A_99)),A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_917,plain,(
    ! [A_192,A_193] :
      ( r2_hidden(k4_tarski('#skF_2'(A_192),'#skF_3'(A_192)),A_193)
      | ~ m1_subset_1(A_192,k1_zfmisc_1(A_193))
      | k1_xboole_0 = A_192
      | ~ v1_relat_1(A_192) ) ),
    inference(resolution,[status(thm)],[c_197,c_22])).

tff(c_18,plain,(
    ! [C_11,A_9,B_10,D_12] :
      ( C_11 = A_9
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_970,plain,(
    ! [C_195,A_196,D_197] :
      ( C_195 = '#skF_2'(A_196)
      | ~ m1_subset_1(A_196,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_195),D_197)))
      | k1_xboole_0 = A_196
      | ~ v1_relat_1(A_196) ) ),
    inference(resolution,[status(thm)],[c_917,c_18])).

tff(c_973,plain,
    ( '#skF_2'('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_970])).

tff(c_980,plain,
    ( '#skF_2'('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_973])).

tff(c_984,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_980])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1028,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_64])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    ! [A_29,B_32] :
      ( k1_funct_1(A_29,B_32) = k1_xboole_0
      | r2_hidden(B_32,k1_relat_1(A_29))
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_134,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_142,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_134])).

tff(c_435,plain,(
    ! [B_119,C_120,A_121] :
      ( r2_hidden(k1_funct_1(B_119,C_120),A_121)
      | ~ r2_hidden(C_120,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v5_relat_1(B_119,A_121)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_447,plain,
    ( ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_435,c_62])).

tff(c_456,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_142,c_70,c_447])).

tff(c_461,plain,
    ( k1_funct_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_456])).

tff(c_467,plain,(
    k1_funct_1('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_70,c_461])).

tff(c_470,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_62])).

tff(c_1010,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_470])).

tff(c_68,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_38,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_81,plain,(
    ! [A_52] : v1_relat_1(k6_relat_1(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_81])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_89,plain,(
    ! [A_54] :
      ( v1_funct_1(A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_93,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_89])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_291,plain,(
    ! [A_110,B_111] :
      ( k1_funct_1(A_110,B_111) = k1_xboole_0
      | r2_hidden(B_111,k1_relat_1(A_110))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_307,plain,(
    ! [B_111] :
      ( k1_funct_1(k1_xboole_0,B_111) = k1_xboole_0
      | r2_hidden(B_111,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_291])).

tff(c_314,plain,(
    ! [B_112] :
      ( k1_funct_1(k1_xboole_0,B_112) = k1_xboole_0
      | r2_hidden(B_112,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_93,c_307])).

tff(c_52,plain,(
    ! [B_39,A_38] :
      ( ~ r1_tarski(B_39,A_38)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_327,plain,(
    ! [B_112] :
      ( ~ r1_tarski(k1_xboole_0,B_112)
      | k1_funct_1(k1_xboole_0,B_112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_314,c_52])).

tff(c_337,plain,(
    ! [B_112] : k1_funct_1(k1_xboole_0,B_112) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_327])).

tff(c_1014,plain,(
    ! [B_112] : k1_funct_1('#skF_6',B_112) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_984,c_337])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_565,plain,(
    ! [D_130,C_131,B_132,A_133] :
      ( r2_hidden(k1_funct_1(D_130,C_131),B_132)
      | k1_xboole_0 = B_132
      | ~ r2_hidden(C_131,A_133)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132)))
      | ~ v1_funct_2(D_130,A_133,B_132)
      | ~ v1_funct_1(D_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_589,plain,(
    ! [D_130,A_19,B_132,B_20] :
      ( r2_hidden(k1_funct_1(D_130,A_19),B_132)
      | k1_xboole_0 = B_132
      | ~ m1_subset_1(D_130,k1_zfmisc_1(k2_zfmisc_1(B_20,B_132)))
      | ~ v1_funct_2(D_130,B_20,B_132)
      | ~ v1_funct_1(D_130)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_24,c_565])).

tff(c_2772,plain,(
    ! [D_335,A_336,B_337,B_338] :
      ( r2_hidden(k1_funct_1(D_335,A_336),B_337)
      | B_337 = '#skF_6'
      | ~ m1_subset_1(D_335,k1_zfmisc_1(k2_zfmisc_1(B_338,B_337)))
      | ~ v1_funct_2(D_335,B_338,B_337)
      | ~ v1_funct_1(D_335)
      | v1_xboole_0(B_338)
      | ~ m1_subset_1(A_336,B_338) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_589])).

tff(c_2778,plain,(
    ! [A_336] :
      ( r2_hidden(k1_funct_1('#skF_6',A_336),'#skF_5')
      | '#skF_5' = '#skF_6'
      | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(k1_tarski('#skF_4'))
      | ~ m1_subset_1(A_336,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_66,c_2772])).

tff(c_2793,plain,(
    ! [A_336] :
      ( r2_hidden('#skF_6','#skF_5')
      | '#skF_5' = '#skF_6'
      | v1_xboole_0(k1_tarski('#skF_4'))
      | ~ m1_subset_1(A_336,k1_tarski('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1014,c_2778])).

tff(c_2796,plain,(
    ! [A_339] : ~ m1_subset_1(A_339,k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1028,c_1010,c_2793])).

tff(c_2801,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_20,c_2796])).

tff(c_2803,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_2802,plain,(
    '#skF_2'('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_30,plain,(
    ! [A_22,C_24,B_23] :
      ( r2_hidden(A_22,k1_relat_1(C_24))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_218,plain,(
    ! [A_99] :
      ( r2_hidden('#skF_2'(A_99),k1_relat_1(A_99))
      | k1_xboole_0 = A_99
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_197,c_30])).

tff(c_2816,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2802,c_218])).

tff(c_2832,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_2816])).

tff(c_2834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2803,c_456,c_2832])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:44:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.96  
% 5.02/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.96  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 5.02/1.96  
% 5.02/1.96  %Foreground sorts:
% 5.02/1.96  
% 5.02/1.96  
% 5.02/1.96  %Background operators:
% 5.02/1.96  
% 5.02/1.96  
% 5.02/1.96  %Foreground operators:
% 5.02/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.02/1.96  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.02/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.02/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.02/1.96  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.02/1.96  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.02/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.02/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.02/1.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.02/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.02/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.02/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.02/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.02/1.96  tff('#skF_6', type, '#skF_6': $i).
% 5.02/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.02/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.02/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.02/1.96  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.02/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.02/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.02/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.02/1.96  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.02/1.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.02/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.02/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.02/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.02/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.02/1.96  
% 5.02/1.97  tff(f_46, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.02/1.97  tff(f_37, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.02/1.97  tff(f_153, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 5.02/1.97  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.02/1.97  tff(f_77, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 5.02/1.97  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.02/1.97  tff(f_43, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 5.02/1.97  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 5.02/1.97  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.02/1.97  tff(f_114, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 5.02/1.97  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.02/1.97  tff(f_81, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 5.02/1.97  tff(f_61, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 5.02/1.97  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.02/1.97  tff(f_85, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 5.02/1.97  tff(f_80, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.02/1.97  tff(f_119, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.02/1.97  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.02/1.97  tff(f_141, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.02/1.97  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 5.02/1.97  tff(c_20, plain, (![A_13]: (m1_subset_1('#skF_1'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.02/1.97  tff(c_12, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.02/1.97  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.02/1.97  tff(c_123, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.02/1.97  tff(c_131, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_123])).
% 5.02/1.97  tff(c_197, plain, (![A_99]: (k1_xboole_0=A_99 | r2_hidden(k4_tarski('#skF_2'(A_99), '#skF_3'(A_99)), A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.02/1.97  tff(c_22, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.02/1.97  tff(c_917, plain, (![A_192, A_193]: (r2_hidden(k4_tarski('#skF_2'(A_192), '#skF_3'(A_192)), A_193) | ~m1_subset_1(A_192, k1_zfmisc_1(A_193)) | k1_xboole_0=A_192 | ~v1_relat_1(A_192))), inference(resolution, [status(thm)], [c_197, c_22])).
% 5.02/1.97  tff(c_18, plain, (![C_11, A_9, B_10, D_12]: (C_11=A_9 | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.02/1.97  tff(c_970, plain, (![C_195, A_196, D_197]: (C_195='#skF_2'(A_196) | ~m1_subset_1(A_196, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_195), D_197))) | k1_xboole_0=A_196 | ~v1_relat_1(A_196))), inference(resolution, [status(thm)], [c_917, c_18])).
% 5.02/1.97  tff(c_973, plain, ('#skF_2'('#skF_6')='#skF_4' | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_970])).
% 5.02/1.97  tff(c_980, plain, ('#skF_2'('#skF_6')='#skF_4' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_973])).
% 5.02/1.97  tff(c_984, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_980])).
% 5.02/1.97  tff(c_64, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.02/1.97  tff(c_1028, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_984, c_64])).
% 5.02/1.97  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.02/1.97  tff(c_48, plain, (![A_29, B_32]: (k1_funct_1(A_29, B_32)=k1_xboole_0 | r2_hidden(B_32, k1_relat_1(A_29)) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.02/1.97  tff(c_134, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.02/1.97  tff(c_142, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_134])).
% 5.02/1.97  tff(c_435, plain, (![B_119, C_120, A_121]: (r2_hidden(k1_funct_1(B_119, C_120), A_121) | ~r2_hidden(C_120, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v5_relat_1(B_119, A_121) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.02/1.97  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.02/1.97  tff(c_447, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_435, c_62])).
% 5.02/1.97  tff(c_456, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_142, c_70, c_447])).
% 5.02/1.97  tff(c_461, plain, (k1_funct_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_456])).
% 5.02/1.97  tff(c_467, plain, (k1_funct_1('#skF_6', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_131, c_70, c_461])).
% 5.02/1.97  tff(c_470, plain, (~r2_hidden(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_467, c_62])).
% 5.02/1.97  tff(c_1010, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_984, c_470])).
% 5.02/1.97  tff(c_68, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.02/1.97  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.02/1.97  tff(c_38, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.02/1.97  tff(c_81, plain, (![A_52]: (v1_relat_1(k6_relat_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.02/1.97  tff(c_83, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_81])).
% 5.02/1.97  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.02/1.97  tff(c_89, plain, (![A_54]: (v1_funct_1(A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.02/1.97  tff(c_93, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_89])).
% 5.02/1.97  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.02/1.97  tff(c_291, plain, (![A_110, B_111]: (k1_funct_1(A_110, B_111)=k1_xboole_0 | r2_hidden(B_111, k1_relat_1(A_110)) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.02/1.97  tff(c_307, plain, (![B_111]: (k1_funct_1(k1_xboole_0, B_111)=k1_xboole_0 | r2_hidden(B_111, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_291])).
% 5.02/1.97  tff(c_314, plain, (![B_112]: (k1_funct_1(k1_xboole_0, B_112)=k1_xboole_0 | r2_hidden(B_112, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_93, c_307])).
% 5.02/1.97  tff(c_52, plain, (![B_39, A_38]: (~r1_tarski(B_39, A_38) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.02/1.97  tff(c_327, plain, (![B_112]: (~r1_tarski(k1_xboole_0, B_112) | k1_funct_1(k1_xboole_0, B_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_314, c_52])).
% 5.02/1.97  tff(c_337, plain, (![B_112]: (k1_funct_1(k1_xboole_0, B_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_327])).
% 5.02/1.97  tff(c_1014, plain, (![B_112]: (k1_funct_1('#skF_6', B_112)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_984, c_984, c_337])).
% 5.02/1.97  tff(c_24, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.02/1.97  tff(c_565, plain, (![D_130, C_131, B_132, A_133]: (r2_hidden(k1_funct_1(D_130, C_131), B_132) | k1_xboole_0=B_132 | ~r2_hidden(C_131, A_133) | ~m1_subset_1(D_130, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))) | ~v1_funct_2(D_130, A_133, B_132) | ~v1_funct_1(D_130))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.02/1.97  tff(c_589, plain, (![D_130, A_19, B_132, B_20]: (r2_hidden(k1_funct_1(D_130, A_19), B_132) | k1_xboole_0=B_132 | ~m1_subset_1(D_130, k1_zfmisc_1(k2_zfmisc_1(B_20, B_132))) | ~v1_funct_2(D_130, B_20, B_132) | ~v1_funct_1(D_130) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(resolution, [status(thm)], [c_24, c_565])).
% 5.02/1.97  tff(c_2772, plain, (![D_335, A_336, B_337, B_338]: (r2_hidden(k1_funct_1(D_335, A_336), B_337) | B_337='#skF_6' | ~m1_subset_1(D_335, k1_zfmisc_1(k2_zfmisc_1(B_338, B_337))) | ~v1_funct_2(D_335, B_338, B_337) | ~v1_funct_1(D_335) | v1_xboole_0(B_338) | ~m1_subset_1(A_336, B_338))), inference(demodulation, [status(thm), theory('equality')], [c_984, c_589])).
% 5.02/1.97  tff(c_2778, plain, (![A_336]: (r2_hidden(k1_funct_1('#skF_6', A_336), '#skF_5') | '#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0(k1_tarski('#skF_4')) | ~m1_subset_1(A_336, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_66, c_2772])).
% 5.02/1.97  tff(c_2793, plain, (![A_336]: (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | v1_xboole_0(k1_tarski('#skF_4')) | ~m1_subset_1(A_336, k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1014, c_2778])).
% 5.02/1.97  tff(c_2796, plain, (![A_339]: (~m1_subset_1(A_339, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_12, c_1028, c_1010, c_2793])).
% 5.02/1.97  tff(c_2801, plain, $false, inference(resolution, [status(thm)], [c_20, c_2796])).
% 5.02/1.97  tff(c_2803, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_980])).
% 5.02/1.97  tff(c_2802, plain, ('#skF_2'('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_980])).
% 5.02/1.97  tff(c_30, plain, (![A_22, C_24, B_23]: (r2_hidden(A_22, k1_relat_1(C_24)) | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.02/1.97  tff(c_218, plain, (![A_99]: (r2_hidden('#skF_2'(A_99), k1_relat_1(A_99)) | k1_xboole_0=A_99 | ~v1_relat_1(A_99))), inference(resolution, [status(thm)], [c_197, c_30])).
% 5.02/1.97  tff(c_2816, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2802, c_218])).
% 5.02/1.97  tff(c_2832, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_2816])).
% 5.02/1.97  tff(c_2834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2803, c_456, c_2832])).
% 5.02/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.97  
% 5.02/1.97  Inference rules
% 5.02/1.97  ----------------------
% 5.02/1.97  #Ref     : 0
% 5.02/1.97  #Sup     : 569
% 5.02/1.97  #Fact    : 0
% 5.02/1.97  #Define  : 0
% 5.02/1.97  #Split   : 6
% 5.02/1.97  #Chain   : 0
% 5.02/1.97  #Close   : 0
% 5.02/1.97  
% 5.02/1.97  Ordering : KBO
% 5.02/1.97  
% 5.02/1.97  Simplification rules
% 5.02/1.97  ----------------------
% 5.02/1.97  #Subsume      : 121
% 5.02/1.97  #Demod        : 471
% 5.02/1.97  #Tautology    : 162
% 5.02/1.97  #SimpNegUnit  : 30
% 5.02/1.97  #BackRed      : 48
% 5.02/1.97  
% 5.02/1.97  #Partial instantiations: 0
% 5.02/1.97  #Strategies tried      : 1
% 5.02/1.97  
% 5.02/1.97  Timing (in seconds)
% 5.02/1.97  ----------------------
% 5.02/1.98  Preprocessing        : 0.36
% 5.02/1.98  Parsing              : 0.19
% 5.02/1.98  CNF conversion       : 0.02
% 5.02/1.98  Main loop            : 0.86
% 5.02/1.98  Inferencing          : 0.31
% 5.02/1.98  Reduction            : 0.28
% 5.02/1.98  Demodulation         : 0.19
% 5.02/1.98  BG Simplification    : 0.03
% 5.02/1.98  Subsumption          : 0.16
% 5.02/1.98  Abstraction          : 0.04
% 5.02/1.98  MUC search           : 0.00
% 5.02/1.98  Cooper               : 0.00
% 5.02/1.98  Total                : 1.25
% 5.02/1.98  Index Insertion      : 0.00
% 5.02/1.98  Index Deletion       : 0.00
% 5.02/1.98  Index Matching       : 0.00
% 5.02/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
