%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:17 EST 2020

% Result     : Theorem 9.22s
% Output     : CNFRefutation 9.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 282 expanded)
%              Number of leaves         :   52 ( 114 expanded)
%              Depth                    :   16
%              Number of atoms          :  192 ( 592 expanded)
%              Number of equality atoms :   52 ( 168 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_178,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_148,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_105,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_166,axiom,(
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

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_18,plain,(
    ! [A_13] : m1_subset_1('#skF_1'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_133,plain,(
    ! [C_99,A_100,B_101] :
      ( v1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_145,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_133])).

tff(c_40,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_154,plain,
    ( k1_relat_1('#skF_8') != k1_xboole_0
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_145,c_40])).

tff(c_166,plain,(
    k1_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_223,plain,(
    ! [C_114,B_115,A_116] :
      ( v5_relat_1(C_114,B_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_235,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_223])).

tff(c_82,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_841,plain,(
    ! [B_192,C_193,A_194] :
      ( r2_hidden(k1_funct_1(B_192,C_193),A_194)
      | ~ r2_hidden(C_193,k1_relat_1(B_192))
      | ~ v1_funct_1(B_192)
      | ~ v5_relat_1(B_192,A_194)
      | ~ v1_relat_1(B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_74,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_861,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_841,c_74])).

tff(c_869,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_235,c_82,c_861])).

tff(c_60,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_5'(A_58),A_58)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_36,plain,(
    ! [A_31] :
      ( k10_relat_1(A_31,k2_relat_1(A_31)) = k1_relat_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_505,plain,(
    ! [A_168,B_169,C_170] :
      ( r2_hidden(k4_tarski(A_168,'#skF_2'(A_168,B_169,C_170)),C_170)
      | ~ r2_hidden(A_168,k10_relat_1(C_170,B_169))
      | ~ v1_relat_1(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6599,plain,(
    ! [A_543,B_544,C_545,A_546] :
      ( r2_hidden(k4_tarski(A_543,'#skF_2'(A_543,B_544,C_545)),A_546)
      | ~ m1_subset_1(C_545,k1_zfmisc_1(A_546))
      | ~ r2_hidden(A_543,k10_relat_1(C_545,B_544))
      | ~ v1_relat_1(C_545) ) ),
    inference(resolution,[status(thm)],[c_505,c_20])).

tff(c_16,plain,(
    ! [C_11,A_9,B_10,D_12] :
      ( C_11 = A_9
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9018,plain,(
    ! [C_633,A_630,D_632,B_629,C_631] :
      ( C_631 = A_630
      | ~ m1_subset_1(C_633,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_631),D_632)))
      | ~ r2_hidden(A_630,k10_relat_1(C_633,B_629))
      | ~ v1_relat_1(C_633) ) ),
    inference(resolution,[status(thm)],[c_6599,c_16])).

tff(c_9032,plain,(
    ! [A_630,B_629] :
      ( A_630 = '#skF_6'
      | ~ r2_hidden(A_630,k10_relat_1('#skF_8',B_629))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_78,c_9018])).

tff(c_9052,plain,(
    ! [A_634,B_635] :
      ( A_634 = '#skF_6'
      | ~ r2_hidden(A_634,k10_relat_1('#skF_8',B_635)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_9032])).

tff(c_9134,plain,(
    ! [A_634] :
      ( A_634 = '#skF_6'
      | ~ r2_hidden(A_634,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_9052])).

tff(c_9172,plain,(
    ! [A_636] :
      ( A_636 = '#skF_6'
      | ~ r2_hidden(A_636,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_9134])).

tff(c_9232,plain,
    ( '#skF_5'(k1_relat_1('#skF_8')) = '#skF_6'
    | k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_9172])).

tff(c_9249,plain,(
    '#skF_5'(k1_relat_1('#skF_8')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_9232])).

tff(c_9283,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_relat_1('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9249,c_60])).

tff(c_9304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_869,c_9283])).

tff(c_9305,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_9314,plain,(
    ! [A_1] : r1_tarski('#skF_8',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9305,c_2])).

tff(c_123,plain,(
    ! [A_97,B_98] :
      ( r2_hidden(A_97,B_98)
      | v1_xboole_0(B_98)
      | ~ m1_subset_1(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_44,plain,(
    ! [B_38,A_37] :
      ( ~ r1_tarski(B_38,A_37)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_9416,plain,(
    ! [B_662,A_663] :
      ( ~ r1_tarski(B_662,A_663)
      | v1_xboole_0(B_662)
      | ~ m1_subset_1(A_663,B_662) ) ),
    inference(resolution,[status(thm)],[c_123,c_44])).

tff(c_9420,plain,(
    ! [A_1] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_1,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9314,c_9416])).

tff(c_9429,plain,(
    ! [A_667] : ~ m1_subset_1(A_667,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_9420])).

tff(c_9434,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_9429])).

tff(c_9435,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_9420])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_9315,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9305,c_76])).

tff(c_80,plain,(
    v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_22,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9313,plain,(
    ! [A_19] : m1_subset_1('#skF_8',k1_zfmisc_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9305,c_22])).

tff(c_72,plain,(
    ! [B_81,A_80,C_82] :
      ( k1_xboole_0 = B_81
      | k1_relset_1(A_80,B_81,C_82) = A_80
      | ~ v1_funct_2(C_82,A_80,B_81)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_10711,plain,(
    ! [B_789,A_790,C_791] :
      ( B_789 = '#skF_8'
      | k1_relset_1(A_790,B_789,C_791) = A_790
      | ~ v1_funct_2(C_791,A_790,B_789)
      | ~ m1_subset_1(C_791,k1_zfmisc_1(k2_zfmisc_1(A_790,B_789))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9305,c_72])).

tff(c_10732,plain,(
    ! [B_792,A_793] :
      ( B_792 = '#skF_8'
      | k1_relset_1(A_793,B_792,'#skF_8') = A_793
      | ~ v1_funct_2('#skF_8',A_793,B_792) ) ),
    inference(resolution,[status(thm)],[c_9313,c_10711])).

tff(c_10741,plain,
    ( '#skF_7' = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_10732])).

tff(c_10748,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_9315,c_10741])).

tff(c_9312,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_5'(A_58),A_58)
      | A_58 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9305,c_60])).

tff(c_12639,plain,(
    ! [D_904,A_905,B_906,C_907] :
      ( r2_hidden(k4_tarski(D_904,'#skF_4'(A_905,B_906,C_907,D_904)),C_907)
      | ~ r2_hidden(D_904,B_906)
      | k1_relset_1(B_906,A_905,C_907) != B_906
      | ~ m1_subset_1(C_907,k1_zfmisc_1(k2_zfmisc_1(B_906,A_905))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_9619,plain,(
    ! [A_698,B_699,C_700] :
      ( r2_hidden('#skF_2'(A_698,B_699,C_700),B_699)
      | ~ r2_hidden(A_698,k10_relat_1(C_700,B_699))
      | ~ v1_relat_1(C_700) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9853,plain,(
    ! [B_721,A_722,C_723] :
      ( ~ r1_tarski(B_721,'#skF_2'(A_722,B_721,C_723))
      | ~ r2_hidden(A_722,k10_relat_1(C_723,B_721))
      | ~ v1_relat_1(C_723) ) ),
    inference(resolution,[status(thm)],[c_9619,c_44])).

tff(c_9887,plain,(
    ! [A_727,C_728] :
      ( ~ r2_hidden(A_727,k10_relat_1(C_728,'#skF_8'))
      | ~ v1_relat_1(C_728) ) ),
    inference(resolution,[status(thm)],[c_9314,c_9853])).

tff(c_9918,plain,(
    ! [C_729] :
      ( ~ v1_relat_1(C_729)
      | k10_relat_1(C_729,'#skF_8') = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_9312,c_9887])).

tff(c_9926,plain,(
    k10_relat_1('#skF_8','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_145,c_9918])).

tff(c_9857,plain,(
    ! [A_722,C_723] :
      ( ~ r2_hidden(A_722,k10_relat_1(C_723,'#skF_8'))
      | ~ v1_relat_1(C_723) ) ),
    inference(resolution,[status(thm)],[c_9314,c_9853])).

tff(c_9930,plain,(
    ! [A_722] :
      ( ~ r2_hidden(A_722,'#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9926,c_9857])).

tff(c_9934,plain,(
    ! [A_722] : ~ r2_hidden(A_722,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_9930])).

tff(c_12691,plain,(
    ! [D_904,B_906,A_905] :
      ( ~ r2_hidden(D_904,B_906)
      | k1_relset_1(B_906,A_905,'#skF_8') != B_906
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(B_906,A_905))) ) ),
    inference(resolution,[status(thm)],[c_12639,c_9934])).

tff(c_12735,plain,(
    ! [D_908,B_909,A_910] :
      ( ~ r2_hidden(D_908,B_909)
      | k1_relset_1(B_909,A_910,'#skF_8') != B_909 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9313,c_12691])).

tff(c_12778,plain,(
    ! [A_911,A_912] :
      ( k1_relset_1(A_911,A_912,'#skF_8') != A_911
      | A_911 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_9312,c_12735])).

tff(c_12792,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_10748,c_12778])).

tff(c_10,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12821,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_12792,c_10])).

tff(c_12828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9435,c_12821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:05:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.22/3.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.22/3.23  
% 9.22/3.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.22/3.23  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 9.22/3.23  
% 9.22/3.23  %Foreground sorts:
% 9.22/3.23  
% 9.22/3.23  
% 9.22/3.23  %Background operators:
% 9.22/3.23  
% 9.22/3.23  
% 9.22/3.23  %Foreground operators:
% 9.22/3.23  tff('#skF_5', type, '#skF_5': $i > $i).
% 9.22/3.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.22/3.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.22/3.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.22/3.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.22/3.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.22/3.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.22/3.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.22/3.23  tff('#skF_7', type, '#skF_7': $i).
% 9.22/3.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.22/3.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.22/3.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.22/3.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.22/3.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.22/3.23  tff('#skF_6', type, '#skF_6': $i).
% 9.22/3.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.22/3.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.22/3.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.22/3.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.22/3.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.22/3.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.22/3.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.22/3.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 9.22/3.23  tff('#skF_8', type, '#skF_8': $i).
% 9.22/3.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.22/3.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.22/3.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.22/3.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.22/3.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.22/3.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.22/3.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.22/3.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.22/3.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.22/3.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.22/3.23  
% 9.22/3.25  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 9.22/3.25  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 9.22/3.25  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.22/3.25  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 9.22/3.25  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.22/3.25  tff(f_100, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 9.22/3.25  tff(f_148, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 9.22/3.25  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 9.22/3.25  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 9.22/3.25  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 9.22/3.25  tff(f_42, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 9.22/3.25  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.22/3.25  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.22/3.25  tff(f_105, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.22/3.25  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.22/3.25  tff(f_166, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.22/3.25  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 9.22/3.25  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 9.22/3.25  tff(c_18, plain, (![A_13]: (m1_subset_1('#skF_1'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.22/3.25  tff(c_78, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.22/3.25  tff(c_133, plain, (![C_99, A_100, B_101]: (v1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.22/3.25  tff(c_145, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_78, c_133])).
% 9.22/3.25  tff(c_40, plain, (![A_32]: (k1_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.22/3.25  tff(c_154, plain, (k1_relat_1('#skF_8')!=k1_xboole_0 | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_145, c_40])).
% 9.22/3.25  tff(c_166, plain, (k1_relat_1('#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_154])).
% 9.22/3.25  tff(c_223, plain, (![C_114, B_115, A_116]: (v5_relat_1(C_114, B_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.22/3.25  tff(c_235, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_78, c_223])).
% 9.22/3.25  tff(c_82, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.22/3.25  tff(c_841, plain, (![B_192, C_193, A_194]: (r2_hidden(k1_funct_1(B_192, C_193), A_194) | ~r2_hidden(C_193, k1_relat_1(B_192)) | ~v1_funct_1(B_192) | ~v5_relat_1(B_192, A_194) | ~v1_relat_1(B_192))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.22/3.25  tff(c_74, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.22/3.25  tff(c_861, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_841, c_74])).
% 9.22/3.25  tff(c_869, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_235, c_82, c_861])).
% 9.22/3.25  tff(c_60, plain, (![A_58]: (r2_hidden('#skF_5'(A_58), A_58) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.22/3.25  tff(c_36, plain, (![A_31]: (k10_relat_1(A_31, k2_relat_1(A_31))=k1_relat_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.22/3.25  tff(c_505, plain, (![A_168, B_169, C_170]: (r2_hidden(k4_tarski(A_168, '#skF_2'(A_168, B_169, C_170)), C_170) | ~r2_hidden(A_168, k10_relat_1(C_170, B_169)) | ~v1_relat_1(C_170))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.22/3.25  tff(c_20, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.22/3.25  tff(c_6599, plain, (![A_543, B_544, C_545, A_546]: (r2_hidden(k4_tarski(A_543, '#skF_2'(A_543, B_544, C_545)), A_546) | ~m1_subset_1(C_545, k1_zfmisc_1(A_546)) | ~r2_hidden(A_543, k10_relat_1(C_545, B_544)) | ~v1_relat_1(C_545))), inference(resolution, [status(thm)], [c_505, c_20])).
% 9.22/3.25  tff(c_16, plain, (![C_11, A_9, B_10, D_12]: (C_11=A_9 | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.22/3.25  tff(c_9018, plain, (![C_633, A_630, D_632, B_629, C_631]: (C_631=A_630 | ~m1_subset_1(C_633, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_631), D_632))) | ~r2_hidden(A_630, k10_relat_1(C_633, B_629)) | ~v1_relat_1(C_633))), inference(resolution, [status(thm)], [c_6599, c_16])).
% 9.22/3.25  tff(c_9032, plain, (![A_630, B_629]: (A_630='#skF_6' | ~r2_hidden(A_630, k10_relat_1('#skF_8', B_629)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_9018])).
% 9.22/3.25  tff(c_9052, plain, (![A_634, B_635]: (A_634='#skF_6' | ~r2_hidden(A_634, k10_relat_1('#skF_8', B_635)))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_9032])).
% 9.22/3.25  tff(c_9134, plain, (![A_634]: (A_634='#skF_6' | ~r2_hidden(A_634, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_9052])).
% 9.22/3.25  tff(c_9172, plain, (![A_636]: (A_636='#skF_6' | ~r2_hidden(A_636, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_9134])).
% 9.22/3.25  tff(c_9232, plain, ('#skF_5'(k1_relat_1('#skF_8'))='#skF_6' | k1_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_9172])).
% 9.22/3.25  tff(c_9249, plain, ('#skF_5'(k1_relat_1('#skF_8'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_166, c_9232])).
% 9.22/3.25  tff(c_9283, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_relat_1('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9249, c_60])).
% 9.22/3.25  tff(c_9304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_869, c_9283])).
% 9.22/3.25  tff(c_9305, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_154])).
% 9.22/3.25  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.22/3.25  tff(c_9314, plain, (![A_1]: (r1_tarski('#skF_8', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_9305, c_2])).
% 9.22/3.25  tff(c_123, plain, (![A_97, B_98]: (r2_hidden(A_97, B_98) | v1_xboole_0(B_98) | ~m1_subset_1(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.22/3.25  tff(c_44, plain, (![B_38, A_37]: (~r1_tarski(B_38, A_37) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.22/3.25  tff(c_9416, plain, (![B_662, A_663]: (~r1_tarski(B_662, A_663) | v1_xboole_0(B_662) | ~m1_subset_1(A_663, B_662))), inference(resolution, [status(thm)], [c_123, c_44])).
% 9.22/3.25  tff(c_9420, plain, (![A_1]: (v1_xboole_0('#skF_8') | ~m1_subset_1(A_1, '#skF_8'))), inference(resolution, [status(thm)], [c_9314, c_9416])).
% 9.22/3.25  tff(c_9429, plain, (![A_667]: (~m1_subset_1(A_667, '#skF_8'))), inference(splitLeft, [status(thm)], [c_9420])).
% 9.22/3.25  tff(c_9434, plain, $false, inference(resolution, [status(thm)], [c_18, c_9429])).
% 9.22/3.25  tff(c_9435, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_9420])).
% 9.22/3.25  tff(c_76, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.22/3.25  tff(c_9315, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9305, c_76])).
% 9.22/3.25  tff(c_80, plain, (v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.22/3.25  tff(c_22, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.22/3.25  tff(c_9313, plain, (![A_19]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_9305, c_22])).
% 9.22/3.25  tff(c_72, plain, (![B_81, A_80, C_82]: (k1_xboole_0=B_81 | k1_relset_1(A_80, B_81, C_82)=A_80 | ~v1_funct_2(C_82, A_80, B_81) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.22/3.25  tff(c_10711, plain, (![B_789, A_790, C_791]: (B_789='#skF_8' | k1_relset_1(A_790, B_789, C_791)=A_790 | ~v1_funct_2(C_791, A_790, B_789) | ~m1_subset_1(C_791, k1_zfmisc_1(k2_zfmisc_1(A_790, B_789))))), inference(demodulation, [status(thm), theory('equality')], [c_9305, c_72])).
% 9.22/3.25  tff(c_10732, plain, (![B_792, A_793]: (B_792='#skF_8' | k1_relset_1(A_793, B_792, '#skF_8')=A_793 | ~v1_funct_2('#skF_8', A_793, B_792))), inference(resolution, [status(thm)], [c_9313, c_10711])).
% 9.22/3.25  tff(c_10741, plain, ('#skF_7'='#skF_8' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_80, c_10732])).
% 9.22/3.25  tff(c_10748, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_9315, c_10741])).
% 9.22/3.25  tff(c_9312, plain, (![A_58]: (r2_hidden('#skF_5'(A_58), A_58) | A_58='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9305, c_60])).
% 9.22/3.25  tff(c_12639, plain, (![D_904, A_905, B_906, C_907]: (r2_hidden(k4_tarski(D_904, '#skF_4'(A_905, B_906, C_907, D_904)), C_907) | ~r2_hidden(D_904, B_906) | k1_relset_1(B_906, A_905, C_907)!=B_906 | ~m1_subset_1(C_907, k1_zfmisc_1(k2_zfmisc_1(B_906, A_905))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.22/3.25  tff(c_9619, plain, (![A_698, B_699, C_700]: (r2_hidden('#skF_2'(A_698, B_699, C_700), B_699) | ~r2_hidden(A_698, k10_relat_1(C_700, B_699)) | ~v1_relat_1(C_700))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.22/3.25  tff(c_9853, plain, (![B_721, A_722, C_723]: (~r1_tarski(B_721, '#skF_2'(A_722, B_721, C_723)) | ~r2_hidden(A_722, k10_relat_1(C_723, B_721)) | ~v1_relat_1(C_723))), inference(resolution, [status(thm)], [c_9619, c_44])).
% 9.22/3.25  tff(c_9887, plain, (![A_727, C_728]: (~r2_hidden(A_727, k10_relat_1(C_728, '#skF_8')) | ~v1_relat_1(C_728))), inference(resolution, [status(thm)], [c_9314, c_9853])).
% 9.22/3.25  tff(c_9918, plain, (![C_729]: (~v1_relat_1(C_729) | k10_relat_1(C_729, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_9312, c_9887])).
% 9.22/3.25  tff(c_9926, plain, (k10_relat_1('#skF_8', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_145, c_9918])).
% 9.22/3.25  tff(c_9857, plain, (![A_722, C_723]: (~r2_hidden(A_722, k10_relat_1(C_723, '#skF_8')) | ~v1_relat_1(C_723))), inference(resolution, [status(thm)], [c_9314, c_9853])).
% 9.22/3.25  tff(c_9930, plain, (![A_722]: (~r2_hidden(A_722, '#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9926, c_9857])).
% 9.22/3.25  tff(c_9934, plain, (![A_722]: (~r2_hidden(A_722, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_9930])).
% 9.22/3.25  tff(c_12691, plain, (![D_904, B_906, A_905]: (~r2_hidden(D_904, B_906) | k1_relset_1(B_906, A_905, '#skF_8')!=B_906 | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(B_906, A_905))))), inference(resolution, [status(thm)], [c_12639, c_9934])).
% 9.22/3.25  tff(c_12735, plain, (![D_908, B_909, A_910]: (~r2_hidden(D_908, B_909) | k1_relset_1(B_909, A_910, '#skF_8')!=B_909)), inference(demodulation, [status(thm), theory('equality')], [c_9313, c_12691])).
% 9.22/3.25  tff(c_12778, plain, (![A_911, A_912]: (k1_relset_1(A_911, A_912, '#skF_8')!=A_911 | A_911='#skF_8')), inference(resolution, [status(thm)], [c_9312, c_12735])).
% 9.22/3.25  tff(c_12792, plain, (k1_tarski('#skF_6')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_10748, c_12778])).
% 9.22/3.25  tff(c_10, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.22/3.25  tff(c_12821, plain, (~v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_12792, c_10])).
% 9.22/3.25  tff(c_12828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9435, c_12821])).
% 9.22/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.22/3.25  
% 9.22/3.25  Inference rules
% 9.22/3.25  ----------------------
% 9.22/3.25  #Ref     : 0
% 9.22/3.25  #Sup     : 2798
% 9.22/3.25  #Fact    : 0
% 9.22/3.25  #Define  : 0
% 9.22/3.25  #Split   : 15
% 9.22/3.25  #Chain   : 0
% 9.22/3.25  #Close   : 0
% 9.22/3.25  
% 9.22/3.25  Ordering : KBO
% 9.22/3.25  
% 9.22/3.25  Simplification rules
% 9.22/3.25  ----------------------
% 9.22/3.25  #Subsume      : 684
% 9.22/3.25  #Demod        : 2001
% 9.22/3.25  #Tautology    : 821
% 9.22/3.25  #SimpNegUnit  : 21
% 9.22/3.25  #BackRed      : 17
% 9.22/3.25  
% 9.22/3.25  #Partial instantiations: 0
% 9.22/3.25  #Strategies tried      : 1
% 9.22/3.25  
% 9.22/3.25  Timing (in seconds)
% 9.22/3.25  ----------------------
% 9.22/3.25  Preprocessing        : 0.44
% 9.22/3.25  Parsing              : 0.23
% 9.22/3.25  CNF conversion       : 0.03
% 9.22/3.25  Main loop            : 2.01
% 9.22/3.25  Inferencing          : 0.58
% 9.22/3.25  Reduction            : 0.65
% 9.22/3.25  Demodulation         : 0.47
% 9.22/3.25  BG Simplification    : 0.07
% 9.22/3.25  Subsumption          : 0.56
% 9.22/3.25  Abstraction          : 0.09
% 9.22/3.25  MUC search           : 0.00
% 9.22/3.25  Cooper               : 0.00
% 9.22/3.25  Total                : 2.49
% 9.22/3.25  Index Insertion      : 0.00
% 9.22/3.25  Index Deletion       : 0.00
% 9.22/3.25  Index Matching       : 0.00
% 9.22/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
