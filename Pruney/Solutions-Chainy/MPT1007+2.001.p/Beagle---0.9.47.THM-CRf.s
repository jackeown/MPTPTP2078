%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:11 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 265 expanded)
%              Number of leaves         :   48 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 ( 628 expanded)
%              Number of equality atoms :   41 ( 145 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_37,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_154,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_104,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_142,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1('#skF_1'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_119,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_127,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_119])).

tff(c_182,plain,(
    ! [A_92] :
      ( k1_xboole_0 = A_92
      | r2_hidden(k4_tarski('#skF_2'(A_92),'#skF_3'(A_92)),A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_947,plain,(
    ! [A_181,A_182] :
      ( r2_hidden(k4_tarski('#skF_2'(A_181),'#skF_3'(A_181)),A_182)
      | ~ m1_subset_1(A_181,k1_zfmisc_1(A_182))
      | k1_xboole_0 = A_181
      | ~ v1_relat_1(A_181) ) ),
    inference(resolution,[status(thm)],[c_182,c_22])).

tff(c_18,plain,(
    ! [C_11,A_9,B_10,D_12] :
      ( C_11 = A_9
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1061,plain,(
    ! [C_184,A_185,D_186] :
      ( C_184 = '#skF_2'(A_185)
      | ~ m1_subset_1(A_185,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_184),D_186)))
      | k1_xboole_0 = A_185
      | ~ v1_relat_1(A_185) ) ),
    inference(resolution,[status(thm)],[c_947,c_18])).

tff(c_1064,plain,
    ( '#skF_2'('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1061])).

tff(c_1071,plain,
    ( '#skF_2'('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_1064])).

tff(c_1075,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1071])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1120,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_62])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    ! [A_29,B_32] :
      ( k1_funct_1(A_29,B_32) = k1_xboole_0
      | r2_hidden(B_32,k1_relat_1(A_29))
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_136,plain,(
    ! [C_69,B_70,A_71] :
      ( v5_relat_1(C_69,B_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_144,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_136])).

tff(c_432,plain,(
    ! [B_119,C_120,A_121] :
      ( r2_hidden(k1_funct_1(B_119,C_120),A_121)
      | ~ r2_hidden(C_120,k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v5_relat_1(B_119,A_121)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_60,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_444,plain,
    ( ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_432,c_60])).

tff(c_453,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_144,c_68,c_444])).

tff(c_458,plain,
    ( k1_funct_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_453])).

tff(c_464,plain,(
    k1_funct_1('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_68,c_458])).

tff(c_467,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_60])).

tff(c_1103,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_467])).

tff(c_66,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_85,plain,(
    ! [A_54] :
      ( v1_relat_1(A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_89,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_85])).

tff(c_79,plain,(
    ! [A_52] :
      ( v1_funct_1(A_52)
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_83,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_296,plain,(
    ! [A_111,B_112] :
      ( k1_funct_1(A_111,B_112) = k1_xboole_0
      | r2_hidden(B_112,k1_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_312,plain,(
    ! [B_112] :
      ( k1_funct_1(k1_xboole_0,B_112) = k1_xboole_0
      | r2_hidden(B_112,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_296])).

tff(c_319,plain,(
    ! [B_113] :
      ( k1_funct_1(k1_xboole_0,B_113) = k1_xboole_0
      | r2_hidden(B_113,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_83,c_312])).

tff(c_50,plain,(
    ! [B_39,A_38] :
      ( ~ r1_tarski(B_39,A_38)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_332,plain,(
    ! [B_113] :
      ( ~ r1_tarski(k1_xboole_0,B_113)
      | k1_funct_1(k1_xboole_0,B_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_319,c_50])).

tff(c_342,plain,(
    ! [B_113] : k1_funct_1(k1_xboole_0,B_113) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_332])).

tff(c_1106,plain,(
    ! [B_113] : k1_funct_1('#skF_6',B_113) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_1075,c_342])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_618,plain,(
    ! [D_138,C_139,B_140,A_141] :
      ( r2_hidden(k1_funct_1(D_138,C_139),B_140)
      | k1_xboole_0 = B_140
      | ~ r2_hidden(C_139,A_141)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2(D_138,A_141,B_140)
      | ~ v1_funct_1(D_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_645,plain,(
    ! [D_138,A_19,B_140,B_20] :
      ( r2_hidden(k1_funct_1(D_138,A_19),B_140)
      | k1_xboole_0 = B_140
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(B_20,B_140)))
      | ~ v1_funct_2(D_138,B_20,B_140)
      | ~ v1_funct_1(D_138)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_24,c_618])).

tff(c_3815,plain,(
    ! [D_381,A_382,B_383,B_384] :
      ( r2_hidden(k1_funct_1(D_381,A_382),B_383)
      | B_383 = '#skF_6'
      | ~ m1_subset_1(D_381,k1_zfmisc_1(k2_zfmisc_1(B_384,B_383)))
      | ~ v1_funct_2(D_381,B_384,B_383)
      | ~ v1_funct_1(D_381)
      | v1_xboole_0(B_384)
      | ~ m1_subset_1(A_382,B_384) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_645])).

tff(c_3823,plain,(
    ! [A_382] :
      ( r2_hidden(k1_funct_1('#skF_6',A_382),'#skF_5')
      | '#skF_5' = '#skF_6'
      | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(k1_tarski('#skF_4'))
      | ~ m1_subset_1(A_382,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_64,c_3815])).

tff(c_3842,plain,(
    ! [A_382] :
      ( r2_hidden('#skF_6','#skF_5')
      | '#skF_5' = '#skF_6'
      | v1_xboole_0(k1_tarski('#skF_4'))
      | ~ m1_subset_1(A_382,k1_tarski('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1106,c_3823])).

tff(c_3845,plain,(
    ! [A_385] : ~ m1_subset_1(A_385,k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1120,c_1103,c_3842])).

tff(c_3850,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_20,c_3845])).

tff(c_3852,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1071])).

tff(c_3851,plain,(
    '#skF_2'('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1071])).

tff(c_30,plain,(
    ! [A_22,C_24,B_23] :
      ( r2_hidden(A_22,k1_relat_1(C_24))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_195,plain,(
    ! [A_92] :
      ( r2_hidden('#skF_2'(A_92),k1_relat_1(A_92))
      | k1_xboole_0 = A_92
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_182,c_30])).

tff(c_3865,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3851,c_195])).

tff(c_3881,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_3865])).

tff(c_3883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3852,c_453,c_3881])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:29:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.75/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.20  
% 5.75/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.21  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 5.75/2.21  
% 5.75/2.21  %Foreground sorts:
% 5.75/2.21  
% 5.75/2.21  
% 5.75/2.21  %Background operators:
% 5.75/2.21  
% 5.75/2.21  
% 5.75/2.21  %Foreground operators:
% 5.75/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.75/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.75/2.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.75/2.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.75/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.75/2.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.75/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.75/2.21  tff('#skF_5', type, '#skF_5': $i).
% 5.75/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.75/2.21  tff('#skF_6', type, '#skF_6': $i).
% 5.75/2.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.75/2.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.75/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.75/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.21  tff('#skF_4', type, '#skF_4': $i).
% 5.75/2.21  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.75/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.75/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.21  
% 6.08/2.23  tff(f_46, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.08/2.23  tff(f_37, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.08/2.23  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 6.08/2.23  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.08/2.23  tff(f_79, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 6.08/2.23  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.08/2.23  tff(f_43, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 6.08/2.23  tff(f_104, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 6.08/2.23  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.08/2.23  tff(f_115, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 6.08/2.23  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.08/2.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.08/2.23  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 6.08/2.23  tff(f_86, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 6.08/2.23  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.08/2.23  tff(f_120, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.08/2.23  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.08/2.23  tff(f_142, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 6.08/2.23  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 6.08/2.23  tff(c_20, plain, (![A_13]: (m1_subset_1('#skF_1'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.08/2.23  tff(c_12, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.08/2.23  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.08/2.23  tff(c_119, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.08/2.23  tff(c_127, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_119])).
% 6.08/2.23  tff(c_182, plain, (![A_92]: (k1_xboole_0=A_92 | r2_hidden(k4_tarski('#skF_2'(A_92), '#skF_3'(A_92)), A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.08/2.23  tff(c_22, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.08/2.23  tff(c_947, plain, (![A_181, A_182]: (r2_hidden(k4_tarski('#skF_2'(A_181), '#skF_3'(A_181)), A_182) | ~m1_subset_1(A_181, k1_zfmisc_1(A_182)) | k1_xboole_0=A_181 | ~v1_relat_1(A_181))), inference(resolution, [status(thm)], [c_182, c_22])).
% 6.08/2.23  tff(c_18, plain, (![C_11, A_9, B_10, D_12]: (C_11=A_9 | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.08/2.23  tff(c_1061, plain, (![C_184, A_185, D_186]: (C_184='#skF_2'(A_185) | ~m1_subset_1(A_185, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_184), D_186))) | k1_xboole_0=A_185 | ~v1_relat_1(A_185))), inference(resolution, [status(thm)], [c_947, c_18])).
% 6.08/2.23  tff(c_1064, plain, ('#skF_2'('#skF_6')='#skF_4' | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_1061])).
% 6.08/2.23  tff(c_1071, plain, ('#skF_2'('#skF_6')='#skF_4' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_1064])).
% 6.08/2.23  tff(c_1075, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_1071])).
% 6.08/2.23  tff(c_62, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.08/2.23  tff(c_1120, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_62])).
% 6.08/2.23  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.08/2.23  tff(c_46, plain, (![A_29, B_32]: (k1_funct_1(A_29, B_32)=k1_xboole_0 | r2_hidden(B_32, k1_relat_1(A_29)) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.08/2.23  tff(c_136, plain, (![C_69, B_70, A_71]: (v5_relat_1(C_69, B_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.08/2.23  tff(c_144, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_136])).
% 6.08/2.23  tff(c_432, plain, (![B_119, C_120, A_121]: (r2_hidden(k1_funct_1(B_119, C_120), A_121) | ~r2_hidden(C_120, k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v5_relat_1(B_119, A_121) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.08/2.23  tff(c_60, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.08/2.23  tff(c_444, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_432, c_60])).
% 6.08/2.23  tff(c_453, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_144, c_68, c_444])).
% 6.08/2.23  tff(c_458, plain, (k1_funct_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_453])).
% 6.08/2.23  tff(c_464, plain, (k1_funct_1('#skF_6', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_127, c_68, c_458])).
% 6.08/2.23  tff(c_467, plain, (~r2_hidden(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_60])).
% 6.08/2.23  tff(c_1103, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_467])).
% 6.08/2.23  tff(c_66, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.08/2.23  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 6.08/2.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.08/2.23  tff(c_85, plain, (![A_54]: (v1_relat_1(A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.08/2.23  tff(c_89, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_85])).
% 6.08/2.23  tff(c_79, plain, (![A_52]: (v1_funct_1(A_52) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.08/2.23  tff(c_83, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_79])).
% 6.08/2.23  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.08/2.23  tff(c_296, plain, (![A_111, B_112]: (k1_funct_1(A_111, B_112)=k1_xboole_0 | r2_hidden(B_112, k1_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.08/2.23  tff(c_312, plain, (![B_112]: (k1_funct_1(k1_xboole_0, B_112)=k1_xboole_0 | r2_hidden(B_112, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_296])).
% 6.08/2.23  tff(c_319, plain, (![B_113]: (k1_funct_1(k1_xboole_0, B_113)=k1_xboole_0 | r2_hidden(B_113, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_83, c_312])).
% 6.08/2.23  tff(c_50, plain, (![B_39, A_38]: (~r1_tarski(B_39, A_38) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.08/2.23  tff(c_332, plain, (![B_113]: (~r1_tarski(k1_xboole_0, B_113) | k1_funct_1(k1_xboole_0, B_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_319, c_50])).
% 6.08/2.23  tff(c_342, plain, (![B_113]: (k1_funct_1(k1_xboole_0, B_113)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_332])).
% 6.08/2.23  tff(c_1106, plain, (![B_113]: (k1_funct_1('#skF_6', B_113)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_1075, c_342])).
% 6.08/2.23  tff(c_24, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.08/2.23  tff(c_618, plain, (![D_138, C_139, B_140, A_141]: (r2_hidden(k1_funct_1(D_138, C_139), B_140) | k1_xboole_0=B_140 | ~r2_hidden(C_139, A_141) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2(D_138, A_141, B_140) | ~v1_funct_1(D_138))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.08/2.23  tff(c_645, plain, (![D_138, A_19, B_140, B_20]: (r2_hidden(k1_funct_1(D_138, A_19), B_140) | k1_xboole_0=B_140 | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(B_20, B_140))) | ~v1_funct_2(D_138, B_20, B_140) | ~v1_funct_1(D_138) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(resolution, [status(thm)], [c_24, c_618])).
% 6.08/2.23  tff(c_3815, plain, (![D_381, A_382, B_383, B_384]: (r2_hidden(k1_funct_1(D_381, A_382), B_383) | B_383='#skF_6' | ~m1_subset_1(D_381, k1_zfmisc_1(k2_zfmisc_1(B_384, B_383))) | ~v1_funct_2(D_381, B_384, B_383) | ~v1_funct_1(D_381) | v1_xboole_0(B_384) | ~m1_subset_1(A_382, B_384))), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_645])).
% 6.08/2.23  tff(c_3823, plain, (![A_382]: (r2_hidden(k1_funct_1('#skF_6', A_382), '#skF_5') | '#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0(k1_tarski('#skF_4')) | ~m1_subset_1(A_382, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_64, c_3815])).
% 6.08/2.23  tff(c_3842, plain, (![A_382]: (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | v1_xboole_0(k1_tarski('#skF_4')) | ~m1_subset_1(A_382, k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1106, c_3823])).
% 6.08/2.23  tff(c_3845, plain, (![A_385]: (~m1_subset_1(A_385, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_12, c_1120, c_1103, c_3842])).
% 6.08/2.23  tff(c_3850, plain, $false, inference(resolution, [status(thm)], [c_20, c_3845])).
% 6.08/2.23  tff(c_3852, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_1071])).
% 6.08/2.23  tff(c_3851, plain, ('#skF_2'('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1071])).
% 6.08/2.23  tff(c_30, plain, (![A_22, C_24, B_23]: (r2_hidden(A_22, k1_relat_1(C_24)) | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.08/2.23  tff(c_195, plain, (![A_92]: (r2_hidden('#skF_2'(A_92), k1_relat_1(A_92)) | k1_xboole_0=A_92 | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_182, c_30])).
% 6.08/2.23  tff(c_3865, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | k1_xboole_0='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3851, c_195])).
% 6.08/2.23  tff(c_3881, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_3865])).
% 6.08/2.23  tff(c_3883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3852, c_453, c_3881])).
% 6.08/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.23  
% 6.08/2.23  Inference rules
% 6.08/2.23  ----------------------
% 6.08/2.23  #Ref     : 0
% 6.08/2.23  #Sup     : 786
% 6.08/2.23  #Fact    : 0
% 6.08/2.23  #Define  : 0
% 6.08/2.23  #Split   : 6
% 6.08/2.23  #Chain   : 0
% 6.08/2.23  #Close   : 0
% 6.08/2.23  
% 6.08/2.23  Ordering : KBO
% 6.08/2.23  
% 6.08/2.23  Simplification rules
% 6.08/2.23  ----------------------
% 6.08/2.23  #Subsume      : 178
% 6.08/2.23  #Demod        : 886
% 6.08/2.23  #Tautology    : 290
% 6.08/2.23  #SimpNegUnit  : 48
% 6.08/2.23  #BackRed      : 55
% 6.08/2.23  
% 6.08/2.23  #Partial instantiations: 0
% 6.08/2.23  #Strategies tried      : 1
% 6.08/2.23  
% 6.08/2.23  Timing (in seconds)
% 6.08/2.23  ----------------------
% 6.08/2.23  Preprocessing        : 0.36
% 6.08/2.23  Parsing              : 0.20
% 6.08/2.23  CNF conversion       : 0.02
% 6.08/2.23  Main loop            : 1.04
% 6.08/2.23  Inferencing          : 0.37
% 6.08/2.23  Reduction            : 0.35
% 6.08/2.23  Demodulation         : 0.24
% 6.08/2.23  BG Simplification    : 0.04
% 6.08/2.23  Subsumption          : 0.20
% 6.08/2.23  Abstraction          : 0.04
% 6.08/2.23  MUC search           : 0.00
% 6.08/2.23  Cooper               : 0.00
% 6.08/2.23  Total                : 1.44
% 6.08/2.23  Index Insertion      : 0.00
% 6.08/2.23  Index Deletion       : 0.00
% 6.08/2.23  Index Matching       : 0.00
% 6.08/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
