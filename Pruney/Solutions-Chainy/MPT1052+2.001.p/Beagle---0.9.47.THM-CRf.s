%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:08 EST 2020

% Result     : Theorem 10.89s
% Output     : CNFRefutation 11.19s
% Verified   : 
% Statistics : Number of formulae       :  263 (1343 expanded)
%              Number of leaves         :   47 ( 438 expanded)
%              Depth                    :   15
%              Number of atoms          :  485 (3089 expanded)
%              Number of equality atoms :  186 (1087 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_176,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_120,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_94,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_142,axiom,(
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

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_358,plain,(
    ! [A_85,B_86] :
      ( v1_xboole_0(k1_funct_2(A_85,B_86))
      | ~ v1_xboole_0(B_86)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_90,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_145,plain,(
    ! [B_61,A_62] :
      ( ~ r2_hidden(B_61,A_62)
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_145])).

tff(c_368,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_149])).

tff(c_384,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_88,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_150,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_56,plain,(
    ! [A_28] : k1_relat_1('#skF_2'(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_60,plain,(
    ! [A_28] : v1_relat_1('#skF_2'(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_196,plain,(
    ! [A_71] :
      ( k1_relat_1(A_71) != k1_xboole_0
      | k1_xboole_0 = A_71
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_205,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_2'(A_28)) != k1_xboole_0
      | '#skF_2'(A_28) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60,c_196])).

tff(c_215,plain,(
    ! [A_28] :
      ( k1_xboole_0 != A_28
      | '#skF_2'(A_28) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_205])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_54] :
      ( v1_relat_1(A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_114,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_872,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(k1_relat_1(A_152),k1_relat_1(B_153))
      | ~ r1_tarski(A_152,B_153)
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_892,plain,(
    ! [A_152] :
      ( r1_tarski(k1_relat_1(A_152),k1_xboole_0)
      | ~ r1_tarski(A_152,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_872])).

tff(c_1134,plain,(
    ! [A_170] :
      ( r1_tarski(k1_relat_1(A_170),k1_xboole_0)
      | ~ r1_tarski(A_170,k1_xboole_0)
      | ~ v1_relat_1(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_892])).

tff(c_1151,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,k1_xboole_0)
      | ~ r1_tarski('#skF_2'(A_28),k1_xboole_0)
      | ~ v1_relat_1('#skF_2'(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1134])).

tff(c_1167,plain,(
    ! [A_171] :
      ( r1_tarski(A_171,k1_xboole_0)
      | ~ r1_tarski('#skF_2'(A_171),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1151])).

tff(c_1173,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 != A_28 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_1167])).

tff(c_1205,plain,(
    ! [A_174] :
      ( r1_tarski(A_174,k1_xboole_0)
      | k1_xboole_0 != A_174 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1173])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_677,plain,(
    ! [A_120,C_121,B_122] :
      ( m1_subset_1(A_120,C_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(C_121))
      | ~ r2_hidden(A_120,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_701,plain,(
    ! [A_128,B_129,A_130] :
      ( m1_subset_1(A_128,B_129)
      | ~ r2_hidden(A_128,A_130)
      | ~ r1_tarski(A_130,B_129) ) ),
    inference(resolution,[status(thm)],[c_24,c_677])).

tff(c_714,plain,(
    ! [A_132,B_133] :
      ( m1_subset_1('#skF_1'(A_132),B_133)
      | ~ r1_tarski(A_132,B_133)
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_4,c_701])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_841,plain,(
    ! [A_149,B_150] :
      ( r1_tarski('#skF_1'(A_149),B_150)
      | ~ r1_tarski(A_149,k1_zfmisc_1(B_150))
      | v1_xboole_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_714,c_22])).

tff(c_18,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_850,plain,(
    ! [A_151] :
      ( '#skF_1'(A_151) = k1_xboole_0
      | ~ r1_tarski(A_151,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_841,c_18])).

tff(c_871,plain,
    ( '#skF_1'(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_14,c_850])).

tff(c_906,plain,(
    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_871])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_916,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_906,c_8])).

tff(c_849,plain,(
    ! [A_149] :
      ( '#skF_1'(A_149) = k1_xboole_0
      | ~ r1_tarski(A_149,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_841,c_18])).

tff(c_919,plain,(
    ! [A_149] :
      ( '#skF_1'(A_149) = k1_xboole_0
      | ~ r1_tarski(A_149,k1_xboole_0)
      | v1_xboole_0(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_849])).

tff(c_1336,plain,(
    ! [A_183] :
      ( '#skF_1'(A_183) = k1_xboole_0
      | v1_xboole_0(A_183)
      | k1_xboole_0 != A_183 ) ),
    inference(resolution,[status(thm)],[c_1205,c_919])).

tff(c_1352,plain,
    ( '#skF_1'('#skF_4') = k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1336,c_384])).

tff(c_1356,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1352])).

tff(c_392,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_funct_2(C_91,A_92,B_93)
      | ~ r2_hidden(C_91,k1_funct_2(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_401,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_392])).

tff(c_684,plain,(
    ! [C_123,A_124,B_125] :
      ( m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ r2_hidden(C_123,k1_funct_2(A_124,B_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_736,plain,(
    ! [C_136,A_137,B_138] :
      ( r1_tarski(C_136,k2_zfmisc_1(A_137,B_138))
      | ~ r2_hidden(C_136,k1_funct_2(A_137,B_138)) ) ),
    inference(resolution,[status(thm)],[c_684,c_22])).

tff(c_757,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_736])).

tff(c_768,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2573,plain,(
    ! [A_238,B_239,A_240] :
      ( k1_relset_1(A_238,B_239,A_240) = k1_relat_1(A_240)
      | ~ r1_tarski(A_240,k2_zfmisc_1(A_238,B_239)) ) ),
    inference(resolution,[status(thm)],[c_24,c_768])).

tff(c_2608,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_757,c_2573])).

tff(c_1371,plain,(
    ! [B_185,A_186,C_187] :
      ( k1_xboole_0 = B_185
      | k1_relset_1(A_186,B_185,C_187) = A_186
      | ~ v1_funct_2(C_187,A_186,B_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_13744,plain,(
    ! [B_477,A_478,A_479] :
      ( k1_xboole_0 = B_477
      | k1_relset_1(A_478,B_477,A_479) = A_478
      | ~ v1_funct_2(A_479,A_478,B_477)
      | ~ r1_tarski(A_479,k2_zfmisc_1(A_478,B_477)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1371])).

tff(c_13770,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_757,c_13744])).

tff(c_13786,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_2608,c_13770])).

tff(c_13788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_1356,c_13786])).

tff(c_13790,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1352])).

tff(c_13858,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13790,c_6])).

tff(c_13860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_384,c_13858])).

tff(c_13862,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_13877,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13862,c_8])).

tff(c_13861,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_13869,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13861,c_8])).

tff(c_13906,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13877,c_13869])).

tff(c_94,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_175,plain,(
    ! [A_70] :
      ( k2_relat_1(A_70) != k1_xboole_0
      | k1_xboole_0 = A_70
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_194,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_94,c_175])).

tff(c_195,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_13889,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13869,c_195])).

tff(c_13965,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13906,c_13889])).

tff(c_13934,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13906,c_90])).

tff(c_151,plain,(
    ! [A_63,B_64] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_63,B_64)),B_64) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_156,plain,(
    ! [A_63] : k2_relat_1(k2_zfmisc_1(A_63,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_151,c_18])).

tff(c_13892,plain,(
    ! [A_63] : k2_relat_1(k2_zfmisc_1(A_63,'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13869,c_13869,c_156])).

tff(c_14032,plain,(
    ! [A_63] : k2_relat_1(k2_zfmisc_1(A_63,'#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13906,c_13906,c_13892])).

tff(c_30,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_188,plain,(
    ! [A_17,B_18] :
      ( k2_relat_1(k2_zfmisc_1(A_17,B_18)) != k1_xboole_0
      | k2_zfmisc_1(A_17,B_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_175])).

tff(c_14412,plain,(
    ! [A_523,B_524] :
      ( k2_relat_1(k2_zfmisc_1(A_523,B_524)) != '#skF_4'
      | k2_zfmisc_1(A_523,B_524) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13877,c_13877,c_188])).

tff(c_14427,plain,(
    ! [A_526] : k2_zfmisc_1(A_526,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_14032,c_14412])).

tff(c_78,plain,(
    ! [C_44,A_42,B_43] :
      ( m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ r2_hidden(C_44,k1_funct_2(A_42,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_15302,plain,(
    ! [C_577,A_578] :
      ( m1_subset_1(C_577,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(C_577,k1_funct_2(A_578,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14427,c_78])).

tff(c_15323,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_13934,c_15302])).

tff(c_15331,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_15323,c_22])).

tff(c_13897,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13869,c_16])).

tff(c_13955,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13906,c_13897])).

tff(c_28,plain,(
    ! [A_16] :
      ( v1_relat_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_13878,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_13862,c_28])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_13899,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13869,c_13869,c_42])).

tff(c_13960,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13906,c_13906,c_13899])).

tff(c_14568,plain,(
    ! [A_545,B_546] :
      ( r1_tarski(k2_relat_1(A_545),k2_relat_1(B_546))
      | ~ r1_tarski(A_545,B_546)
      | ~ v1_relat_1(B_546)
      | ~ v1_relat_1(A_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14582,plain,(
    ! [A_545] :
      ( r1_tarski(k2_relat_1(A_545),'#skF_4')
      | ~ r1_tarski(A_545,'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_545) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13960,c_14568])).

tff(c_14978,plain,(
    ! [A_568] :
      ( r1_tarski(k2_relat_1(A_568),'#skF_4')
      | ~ r1_tarski(A_568,'#skF_4')
      | ~ v1_relat_1(A_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13878,c_14582])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14986,plain,(
    ! [A_568] :
      ( k2_relat_1(A_568) = '#skF_4'
      | ~ r1_tarski('#skF_4',k2_relat_1(A_568))
      | ~ r1_tarski(A_568,'#skF_4')
      | ~ v1_relat_1(A_568) ) ),
    inference(resolution,[status(thm)],[c_14978,c_10])).

tff(c_15000,plain,(
    ! [A_568] :
      ( k2_relat_1(A_568) = '#skF_4'
      | ~ r1_tarski(A_568,'#skF_4')
      | ~ v1_relat_1(A_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13955,c_14986])).

tff(c_15334,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_15331,c_15000])).

tff(c_15345,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_15334])).

tff(c_15347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13965,c_15345])).

tff(c_15348,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_15358,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15348,c_15348,c_44])).

tff(c_15394,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15358,c_150])).

tff(c_15576,plain,(
    ! [A_600,B_601] :
      ( v1_xboole_0(k1_funct_2(A_600,B_601))
      | ~ v1_xboole_0(B_601)
      | v1_xboole_0(A_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_15587,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_15576,c_149])).

tff(c_15589,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_15587])).

tff(c_48,plain,(
    ! [A_26] :
      ( k1_relat_1(A_26) != k1_xboole_0
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15379,plain,(
    ! [A_580] :
      ( k1_relat_1(A_580) != '#skF_5'
      | A_580 = '#skF_5'
      | ~ v1_relat_1(A_580) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15348,c_15348,c_48])).

tff(c_15385,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_2'(A_28)) != '#skF_5'
      | '#skF_2'(A_28) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_60,c_15379])).

tff(c_15391,plain,(
    ! [A_28] :
      ( A_28 != '#skF_5'
      | '#skF_2'(A_28) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_15385])).

tff(c_16285,plain,(
    ! [A_670,B_671] :
      ( r1_tarski(k1_relat_1(A_670),k1_relat_1(B_671))
      | ~ r1_tarski(A_670,B_671)
      | ~ v1_relat_1(B_671)
      | ~ v1_relat_1(A_670) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16299,plain,(
    ! [A_670] :
      ( r1_tarski(k1_relat_1(A_670),'#skF_5')
      | ~ r1_tarski(A_670,'#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_670) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15358,c_16285])).

tff(c_16467,plain,(
    ! [A_685] :
      ( r1_tarski(k1_relat_1(A_685),'#skF_5')
      | ~ r1_tarski(A_685,'#skF_5')
      | ~ v1_relat_1(A_685) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_16299])).

tff(c_16490,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_5')
      | ~ r1_tarski('#skF_2'(A_28),'#skF_5')
      | ~ v1_relat_1('#skF_2'(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_16467])).

tff(c_16529,plain,(
    ! [A_687] :
      ( r1_tarski(A_687,'#skF_5')
      | ~ r1_tarski('#skF_2'(A_687),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_16490])).

tff(c_16535,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_5')
      | ~ r1_tarski('#skF_5','#skF_5')
      | A_28 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15391,c_16529])).

tff(c_16540,plain,(
    ! [A_688] :
      ( r1_tarski(A_688,'#skF_5')
      | A_688 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16535])).

tff(c_15898,plain,(
    ! [A_633,C_634,B_635] :
      ( m1_subset_1(A_633,C_634)
      | ~ m1_subset_1(B_635,k1_zfmisc_1(C_634))
      | ~ r2_hidden(A_633,B_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_15911,plain,(
    ! [A_638,B_639,A_640] :
      ( m1_subset_1(A_638,B_639)
      | ~ r2_hidden(A_638,A_640)
      | ~ r1_tarski(A_640,B_639) ) ),
    inference(resolution,[status(thm)],[c_24,c_15898])).

tff(c_15924,plain,(
    ! [A_642,B_643] :
      ( m1_subset_1('#skF_1'(A_642),B_643)
      | ~ r1_tarski(A_642,B_643)
      | v1_xboole_0(A_642) ) ),
    inference(resolution,[status(thm)],[c_4,c_15911])).

tff(c_15976,plain,(
    ! [A_650,B_651] :
      ( r1_tarski('#skF_1'(A_650),B_651)
      | ~ r1_tarski(A_650,k1_zfmisc_1(B_651))
      | v1_xboole_0(A_650) ) ),
    inference(resolution,[status(thm)],[c_15924,c_22])).

tff(c_15353,plain,(
    ! [A_9] :
      ( A_9 = '#skF_5'
      | ~ r1_tarski(A_9,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15348,c_15348,c_18])).

tff(c_16008,plain,(
    ! [A_657] :
      ( '#skF_1'(A_657) = '#skF_5'
      | ~ r1_tarski(A_657,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(A_657) ) ),
    inference(resolution,[status(thm)],[c_15976,c_15353])).

tff(c_16029,plain,
    ( '#skF_1'(k1_zfmisc_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_14,c_16008])).

tff(c_16030,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_16029])).

tff(c_15354,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15348,c_8])).

tff(c_16084,plain,(
    k1_zfmisc_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16030,c_15354])).

tff(c_15984,plain,(
    ! [A_650] :
      ( '#skF_1'(A_650) = '#skF_5'
      | ~ r1_tarski(A_650,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(A_650) ) ),
    inference(resolution,[status(thm)],[c_15976,c_15353])).

tff(c_16104,plain,(
    ! [A_650] :
      ( '#skF_1'(A_650) = '#skF_5'
      | ~ r1_tarski(A_650,'#skF_5')
      | v1_xboole_0(A_650) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16084,c_15984])).

tff(c_16763,plain,(
    ! [A_697] :
      ( '#skF_1'(A_697) = '#skF_5'
      | v1_xboole_0(A_697)
      | A_697 != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_16540,c_16104])).

tff(c_16779,plain,
    ( '#skF_1'('#skF_4') = '#skF_5'
    | '#skF_5' != '#skF_4' ),
    inference(resolution,[status(thm)],[c_16763,c_15589])).

tff(c_16783,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16779])).

tff(c_15627,plain,(
    ! [C_608,A_609,B_610] :
      ( v1_funct_2(C_608,A_609,B_610)
      | ~ r2_hidden(C_608,k1_funct_2(A_609,B_610)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_15636,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_15627])).

tff(c_20,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_15355,plain,(
    ! [A_10] : m1_subset_1('#skF_5',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15348,c_20])).

tff(c_16138,plain,(
    ! [A_661,B_662,C_663] :
      ( k1_relset_1(A_661,B_662,C_663) = k1_relat_1(C_663)
      | ~ m1_subset_1(C_663,k1_zfmisc_1(k2_zfmisc_1(A_661,B_662))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_16152,plain,(
    ! [A_661,B_662] : k1_relset_1(A_661,B_662,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_15355,c_16138])).

tff(c_16161,plain,(
    ! [A_661,B_662] : k1_relset_1(A_661,B_662,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15358,c_16152])).

tff(c_74,plain,(
    ! [B_38,A_37,C_39] :
      ( k1_xboole_0 = B_38
      | k1_relset_1(A_37,B_38,C_39) = A_37
      | ~ v1_funct_2(C_39,A_37,B_38)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_17193,plain,(
    ! [B_716,A_717,C_718] :
      ( B_716 = '#skF_5'
      | k1_relset_1(A_717,B_716,C_718) = A_717
      | ~ v1_funct_2(C_718,A_717,B_716)
      | ~ m1_subset_1(C_718,k1_zfmisc_1(k2_zfmisc_1(A_717,B_716))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15348,c_74])).

tff(c_17207,plain,(
    ! [B_716,A_717] :
      ( B_716 = '#skF_5'
      | k1_relset_1(A_717,B_716,'#skF_5') = A_717
      | ~ v1_funct_2('#skF_5',A_717,B_716) ) ),
    inference(resolution,[status(thm)],[c_15355,c_17193])).

tff(c_17219,plain,(
    ! [B_719,A_720] :
      ( B_719 = '#skF_5'
      | A_720 = '#skF_5'
      | ~ v1_funct_2('#skF_5',A_720,B_719) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16161,c_17207])).

tff(c_17237,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_15636,c_17219])).

tff(c_17256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15394,c_16783,c_17237])).

tff(c_17258,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16779])).

tff(c_15360,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15348,c_6])).

tff(c_17328,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17258,c_15360])).

tff(c_17334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15589,c_17328])).

tff(c_17335,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_15587])).

tff(c_17339,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_17335,c_15354])).

tff(c_17346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15394,c_17339])).

tff(c_17348,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_17414,plain,(
    ! [A_732] :
      ( k1_relat_1(A_732) != k1_xboole_0
      | k1_xboole_0 = A_732
      | ~ v1_relat_1(A_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_17426,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_94,c_17414])).

tff(c_17435,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17348,c_17426])).

tff(c_17436,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17435])).

tff(c_17977,plain,(
    ! [A_801,B_802] :
      ( r1_tarski(k1_relat_1(A_801),k1_relat_1(B_802))
      | ~ r1_tarski(A_801,B_802)
      | ~ v1_relat_1(B_802)
      | ~ v1_relat_1(A_801) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_17988,plain,(
    ! [B_802] :
      ( r1_tarski('#skF_3',k1_relat_1(B_802))
      | ~ r1_tarski('#skF_5',B_802)
      | ~ v1_relat_1(B_802)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17348,c_17977])).

tff(c_18021,plain,(
    ! [B_803] :
      ( r1_tarski('#skF_3',k1_relat_1(B_803))
      | ~ r1_tarski('#skF_5',B_803)
      | ~ v1_relat_1(B_803) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_17988])).

tff(c_18035,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_5',k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_18021])).

tff(c_18044,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_18035])).

tff(c_18045,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_18044])).

tff(c_32,plain,(
    ! [A_19,B_20] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_19,B_20)),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_17423,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_2'(A_28)) != k1_xboole_0
      | '#skF_2'(A_28) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60,c_17414])).

tff(c_17433,plain,(
    ! [A_28] :
      ( k1_xboole_0 != A_28
      | '#skF_2'(A_28) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_17423])).

tff(c_17997,plain,(
    ! [A_801,A_28] :
      ( r1_tarski(k1_relat_1(A_801),A_28)
      | ~ r1_tarski(A_801,'#skF_2'(A_28))
      | ~ v1_relat_1('#skF_2'(A_28))
      | ~ v1_relat_1(A_801) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_17977])).

tff(c_18978,plain,(
    ! [A_850,A_851] :
      ( r1_tarski(k1_relat_1(A_850),A_851)
      | ~ r1_tarski(A_850,'#skF_2'(A_851))
      | ~ v1_relat_1(A_850) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_17997])).

tff(c_19008,plain,(
    ! [A_28,A_851] :
      ( r1_tarski(A_28,A_851)
      | ~ r1_tarski('#skF_2'(A_28),'#skF_2'(A_851))
      | ~ v1_relat_1('#skF_2'(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_18978])).

tff(c_19065,plain,(
    ! [A_855,A_856] :
      ( r1_tarski(A_855,A_856)
      | ~ r1_tarski('#skF_2'(A_855),'#skF_2'(A_856)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_19008])).

tff(c_19068,plain,(
    ! [A_28,A_856] :
      ( r1_tarski(A_28,A_856)
      | ~ r1_tarski(k1_xboole_0,'#skF_2'(A_856))
      | k1_xboole_0 != A_28 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17433,c_19065])).

tff(c_19082,plain,(
    ! [A_857,A_858] :
      ( r1_tarski(A_857,A_858)
      | k1_xboole_0 != A_857 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_19068])).

tff(c_19268,plain,(
    ! [A_864,A_863] :
      ( A_864 = A_863
      | ~ r1_tarski(A_863,A_864)
      | k1_xboole_0 != A_864 ) ),
    inference(resolution,[status(thm)],[c_19082,c_10])).

tff(c_19354,plain,(
    ! [A_872,B_873] :
      ( k2_relat_1(k2_zfmisc_1(A_872,B_873)) = B_873
      | k1_xboole_0 != B_873 ) ),
    inference(resolution,[status(thm)],[c_32,c_19268])).

tff(c_17382,plain,(
    ! [A_728] :
      ( k2_relat_1(A_728) != k1_xboole_0
      | k1_xboole_0 = A_728
      | ~ v1_relat_1(A_728) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_17395,plain,(
    ! [A_17,B_18] :
      ( k2_relat_1(k2_zfmisc_1(A_17,B_18)) != k1_xboole_0
      | k2_zfmisc_1(A_17,B_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_17382])).

tff(c_19654,plain,(
    ! [B_889,A_890] :
      ( k1_xboole_0 != B_889
      | k2_zfmisc_1(A_890,B_889) = k1_xboole_0
      | k1_xboole_0 != B_889 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19354,c_17395])).

tff(c_19702,plain,(
    ! [A_890,B_889] :
      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
      | k2_zfmisc_1(A_890,B_889) = k1_xboole_0
      | k1_xboole_0 != B_889
      | k1_xboole_0 != B_889 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19654,c_17395])).

tff(c_19732,plain,(
    ! [A_890,B_889] :
      ( k2_zfmisc_1(A_890,B_889) = k1_xboole_0
      | k1_xboole_0 != B_889 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_19702])).

tff(c_17901,plain,(
    ! [C_786,A_787,B_788] :
      ( m1_subset_1(C_786,k1_zfmisc_1(k2_zfmisc_1(A_787,B_788)))
      | ~ r2_hidden(C_786,k1_funct_2(A_787,B_788)) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_20086,plain,(
    ! [C_909,A_910,B_911] :
      ( r1_tarski(C_909,k2_zfmisc_1(A_910,B_911))
      | ~ r2_hidden(C_909,k1_funct_2(A_910,B_911)) ) ),
    inference(resolution,[status(thm)],[c_17901,c_22])).

tff(c_20115,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_20086])).

tff(c_20134,plain,
    ( r1_tarski('#skF_5',k1_xboole_0)
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_19732,c_20115])).

tff(c_20145,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_18045,c_20134])).

tff(c_17347,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( k2_relat_1(k2_zfmisc_1(A_21,B_22)) = B_22
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18136,plain,(
    ! [A_810,B_811] :
      ( r1_tarski(k2_relat_1(A_810),k2_relat_1(B_811))
      | ~ r1_tarski(A_810,B_811)
      | ~ v1_relat_1(B_811)
      | ~ v1_relat_1(A_810) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18144,plain,(
    ! [A_810,B_22,A_21] :
      ( r1_tarski(k2_relat_1(A_810),B_22)
      | ~ r1_tarski(A_810,k2_zfmisc_1(A_21,B_22))
      | ~ v1_relat_1(k2_zfmisc_1(A_21,B_22))
      | ~ v1_relat_1(A_810)
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_18136])).

tff(c_25287,plain,(
    ! [A_1053,B_1054,A_1055] :
      ( r1_tarski(k2_relat_1(A_1053),B_1054)
      | ~ r1_tarski(A_1053,k2_zfmisc_1(A_1055,B_1054))
      | ~ v1_relat_1(A_1053)
      | k1_xboole_0 = B_1054
      | k1_xboole_0 = A_1055 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_18144])).

tff(c_25297,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20115,c_25287])).

tff(c_25321,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_25297])).

tff(c_25323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17436,c_20145,c_17347,c_25321])).

tff(c_25324,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_18044])).

tff(c_25327,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_25324,c_10])).

tff(c_25333,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_25327])).

tff(c_25335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17436,c_25333])).

tff(c_25337,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17435])).

tff(c_25336,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_17435])).

tff(c_25357,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25337,c_25336])).

tff(c_25349,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25336,c_25336,c_42])).

tff(c_25384,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25357,c_25357,c_25349])).

tff(c_17401,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_94,c_17382])).

tff(c_17402,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_17401])).

tff(c_25339,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25336,c_17402])).

tff(c_25362,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25357,c_25357,c_25339])).

tff(c_25405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25384,c_25362])).

tff(c_25406,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_17401])).

tff(c_25416,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25406,c_25406,c_44])).

tff(c_25420,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17348,c_25416])).

tff(c_25415,plain,(
    ! [A_8] : r1_tarski('#skF_5',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25406,c_16])).

tff(c_25464,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25420,c_25415])).

tff(c_25425,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25420,c_25406])).

tff(c_25407,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_17401])).

tff(c_25466,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25425,c_25420,c_25407])).

tff(c_25426,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25420,c_17347])).

tff(c_25505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25464,c_25466,c_25426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:25:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.89/4.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.14/4.22  
% 11.14/4.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/4.22  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 11.19/4.22  
% 11.19/4.22  %Foreground sorts:
% 11.19/4.22  
% 11.19/4.22  
% 11.19/4.22  %Background operators:
% 11.19/4.22  
% 11.19/4.22  
% 11.19/4.22  %Foreground operators:
% 11.19/4.22  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 11.19/4.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.19/4.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.19/4.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.19/4.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.19/4.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.19/4.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.19/4.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.19/4.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.19/4.22  tff('#skF_5', type, '#skF_5': $i).
% 11.19/4.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.19/4.22  tff('#skF_3', type, '#skF_3': $i).
% 11.19/4.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.19/4.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.19/4.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.19/4.22  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 11.19/4.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.19/4.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.19/4.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.19/4.22  tff('#skF_4', type, '#skF_4': $i).
% 11.19/4.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.19/4.22  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 11.19/4.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.19/4.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.19/4.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.19/4.22  
% 11.19/4.26  tff(f_149, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 11.19/4.26  tff(f_176, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_2)).
% 11.19/4.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.19/4.26  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.19/4.26  tff(f_120, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 11.19/4.26  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 11.19/4.26  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.19/4.26  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 11.19/4.26  tff(f_94, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 11.19/4.26  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 11.19/4.26  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.19/4.26  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.19/4.26  tff(f_60, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 11.19/4.26  tff(f_48, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 11.19/4.26  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.19/4.26  tff(f_157, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 11.19/4.26  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.19/4.26  tff(f_142, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.19/4.26  tff(f_68, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 11.19/4.26  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.19/4.26  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.19/4.26  tff(f_80, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 11.19/4.26  tff(c_358, plain, (![A_85, B_86]: (v1_xboole_0(k1_funct_2(A_85, B_86)) | ~v1_xboole_0(B_86) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.19/4.26  tff(c_90, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 11.19/4.26  tff(c_145, plain, (![B_61, A_62]: (~r2_hidden(B_61, A_62) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.19/4.26  tff(c_149, plain, (~v1_xboole_0(k1_funct_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_145])).
% 11.19/4.26  tff(c_368, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_358, c_149])).
% 11.19/4.26  tff(c_384, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_368])).
% 11.19/4.26  tff(c_88, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_176])).
% 11.19/4.26  tff(c_150, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_88])).
% 11.19/4.26  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.19/4.26  tff(c_56, plain, (![A_28]: (k1_relat_1('#skF_2'(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.19/4.26  tff(c_60, plain, (![A_28]: (v1_relat_1('#skF_2'(A_28)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.19/4.26  tff(c_196, plain, (![A_71]: (k1_relat_1(A_71)!=k1_xboole_0 | k1_xboole_0=A_71 | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.19/4.26  tff(c_205, plain, (![A_28]: (k1_relat_1('#skF_2'(A_28))!=k1_xboole_0 | '#skF_2'(A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_196])).
% 11.19/4.26  tff(c_215, plain, (![A_28]: (k1_xboole_0!=A_28 | '#skF_2'(A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_205])).
% 11.19/4.26  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.19/4.26  tff(c_110, plain, (![A_54]: (v1_relat_1(A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.19/4.26  tff(c_114, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_110])).
% 11.19/4.26  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.19/4.26  tff(c_872, plain, (![A_152, B_153]: (r1_tarski(k1_relat_1(A_152), k1_relat_1(B_153)) | ~r1_tarski(A_152, B_153) | ~v1_relat_1(B_153) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.19/4.26  tff(c_892, plain, (![A_152]: (r1_tarski(k1_relat_1(A_152), k1_xboole_0) | ~r1_tarski(A_152, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_152))), inference(superposition, [status(thm), theory('equality')], [c_44, c_872])).
% 11.19/4.26  tff(c_1134, plain, (![A_170]: (r1_tarski(k1_relat_1(A_170), k1_xboole_0) | ~r1_tarski(A_170, k1_xboole_0) | ~v1_relat_1(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_892])).
% 11.19/4.26  tff(c_1151, plain, (![A_28]: (r1_tarski(A_28, k1_xboole_0) | ~r1_tarski('#skF_2'(A_28), k1_xboole_0) | ~v1_relat_1('#skF_2'(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1134])).
% 11.19/4.26  tff(c_1167, plain, (![A_171]: (r1_tarski(A_171, k1_xboole_0) | ~r1_tarski('#skF_2'(A_171), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1151])).
% 11.19/4.26  tff(c_1173, plain, (![A_28]: (r1_tarski(A_28, k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_xboole_0!=A_28)), inference(superposition, [status(thm), theory('equality')], [c_215, c_1167])).
% 11.19/4.26  tff(c_1205, plain, (![A_174]: (r1_tarski(A_174, k1_xboole_0) | k1_xboole_0!=A_174)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1173])).
% 11.19/4.26  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.19/4.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.19/4.26  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.19/4.26  tff(c_677, plain, (![A_120, C_121, B_122]: (m1_subset_1(A_120, C_121) | ~m1_subset_1(B_122, k1_zfmisc_1(C_121)) | ~r2_hidden(A_120, B_122))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.19/4.26  tff(c_701, plain, (![A_128, B_129, A_130]: (m1_subset_1(A_128, B_129) | ~r2_hidden(A_128, A_130) | ~r1_tarski(A_130, B_129))), inference(resolution, [status(thm)], [c_24, c_677])).
% 11.19/4.26  tff(c_714, plain, (![A_132, B_133]: (m1_subset_1('#skF_1'(A_132), B_133) | ~r1_tarski(A_132, B_133) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_4, c_701])).
% 11.19/4.26  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.19/4.26  tff(c_841, plain, (![A_149, B_150]: (r1_tarski('#skF_1'(A_149), B_150) | ~r1_tarski(A_149, k1_zfmisc_1(B_150)) | v1_xboole_0(A_149))), inference(resolution, [status(thm)], [c_714, c_22])).
% 11.19/4.26  tff(c_18, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.19/4.26  tff(c_850, plain, (![A_151]: ('#skF_1'(A_151)=k1_xboole_0 | ~r1_tarski(A_151, k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(A_151))), inference(resolution, [status(thm)], [c_841, c_18])).
% 11.19/4.26  tff(c_871, plain, ('#skF_1'(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_850])).
% 11.19/4.26  tff(c_906, plain, (v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_871])).
% 11.19/4.26  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.19/4.26  tff(c_916, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_906, c_8])).
% 11.19/4.26  tff(c_849, plain, (![A_149]: ('#skF_1'(A_149)=k1_xboole_0 | ~r1_tarski(A_149, k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(A_149))), inference(resolution, [status(thm)], [c_841, c_18])).
% 11.19/4.26  tff(c_919, plain, (![A_149]: ('#skF_1'(A_149)=k1_xboole_0 | ~r1_tarski(A_149, k1_xboole_0) | v1_xboole_0(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_916, c_849])).
% 11.19/4.26  tff(c_1336, plain, (![A_183]: ('#skF_1'(A_183)=k1_xboole_0 | v1_xboole_0(A_183) | k1_xboole_0!=A_183)), inference(resolution, [status(thm)], [c_1205, c_919])).
% 11.19/4.26  tff(c_1352, plain, ('#skF_1'('#skF_4')=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_1336, c_384])).
% 11.19/4.26  tff(c_1356, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_1352])).
% 11.19/4.26  tff(c_392, plain, (![C_91, A_92, B_93]: (v1_funct_2(C_91, A_92, B_93) | ~r2_hidden(C_91, k1_funct_2(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.19/4.26  tff(c_401, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_90, c_392])).
% 11.19/4.26  tff(c_684, plain, (![C_123, A_124, B_125]: (m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~r2_hidden(C_123, k1_funct_2(A_124, B_125)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.19/4.26  tff(c_736, plain, (![C_136, A_137, B_138]: (r1_tarski(C_136, k2_zfmisc_1(A_137, B_138)) | ~r2_hidden(C_136, k1_funct_2(A_137, B_138)))), inference(resolution, [status(thm)], [c_684, c_22])).
% 11.19/4.26  tff(c_757, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_736])).
% 11.19/4.26  tff(c_768, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.19/4.26  tff(c_2573, plain, (![A_238, B_239, A_240]: (k1_relset_1(A_238, B_239, A_240)=k1_relat_1(A_240) | ~r1_tarski(A_240, k2_zfmisc_1(A_238, B_239)))), inference(resolution, [status(thm)], [c_24, c_768])).
% 11.19/4.26  tff(c_2608, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_757, c_2573])).
% 11.19/4.26  tff(c_1371, plain, (![B_185, A_186, C_187]: (k1_xboole_0=B_185 | k1_relset_1(A_186, B_185, C_187)=A_186 | ~v1_funct_2(C_187, A_186, B_185) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.19/4.26  tff(c_13744, plain, (![B_477, A_478, A_479]: (k1_xboole_0=B_477 | k1_relset_1(A_478, B_477, A_479)=A_478 | ~v1_funct_2(A_479, A_478, B_477) | ~r1_tarski(A_479, k2_zfmisc_1(A_478, B_477)))), inference(resolution, [status(thm)], [c_24, c_1371])).
% 11.19/4.26  tff(c_13770, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_757, c_13744])).
% 11.19/4.26  tff(c_13786, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_401, c_2608, c_13770])).
% 11.19/4.26  tff(c_13788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_1356, c_13786])).
% 11.19/4.26  tff(c_13790, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1352])).
% 11.19/4.26  tff(c_13858, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13790, c_6])).
% 11.19/4.26  tff(c_13860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_384, c_13858])).
% 11.19/4.26  tff(c_13862, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_368])).
% 11.19/4.26  tff(c_13877, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_13862, c_8])).
% 11.19/4.26  tff(c_13861, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_368])).
% 11.19/4.26  tff(c_13869, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_13861, c_8])).
% 11.19/4.26  tff(c_13906, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13877, c_13869])).
% 11.19/4.26  tff(c_94, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 11.19/4.26  tff(c_175, plain, (![A_70]: (k2_relat_1(A_70)!=k1_xboole_0 | k1_xboole_0=A_70 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.19/4.26  tff(c_194, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_94, c_175])).
% 11.19/4.26  tff(c_195, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_194])).
% 11.19/4.26  tff(c_13889, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13869, c_195])).
% 11.19/4.26  tff(c_13965, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13906, c_13889])).
% 11.19/4.26  tff(c_13934, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13906, c_90])).
% 11.19/4.26  tff(c_151, plain, (![A_63, B_64]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_63, B_64)), B_64))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.19/4.26  tff(c_156, plain, (![A_63]: (k2_relat_1(k2_zfmisc_1(A_63, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_151, c_18])).
% 11.19/4.26  tff(c_13892, plain, (![A_63]: (k2_relat_1(k2_zfmisc_1(A_63, '#skF_3'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13869, c_13869, c_156])).
% 11.19/4.26  tff(c_14032, plain, (![A_63]: (k2_relat_1(k2_zfmisc_1(A_63, '#skF_4'))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13906, c_13906, c_13892])).
% 11.19/4.26  tff(c_30, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.19/4.26  tff(c_188, plain, (![A_17, B_18]: (k2_relat_1(k2_zfmisc_1(A_17, B_18))!=k1_xboole_0 | k2_zfmisc_1(A_17, B_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_175])).
% 11.19/4.26  tff(c_14412, plain, (![A_523, B_524]: (k2_relat_1(k2_zfmisc_1(A_523, B_524))!='#skF_4' | k2_zfmisc_1(A_523, B_524)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13877, c_13877, c_188])).
% 11.19/4.26  tff(c_14427, plain, (![A_526]: (k2_zfmisc_1(A_526, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14032, c_14412])).
% 11.19/4.26  tff(c_78, plain, (![C_44, A_42, B_43]: (m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~r2_hidden(C_44, k1_funct_2(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.19/4.26  tff(c_15302, plain, (![C_577, A_578]: (m1_subset_1(C_577, k1_zfmisc_1('#skF_4')) | ~r2_hidden(C_577, k1_funct_2(A_578, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14427, c_78])).
% 11.19/4.26  tff(c_15323, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_13934, c_15302])).
% 11.19/4.26  tff(c_15331, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_15323, c_22])).
% 11.19/4.26  tff(c_13897, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_13869, c_16])).
% 11.19/4.26  tff(c_13955, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_13906, c_13897])).
% 11.19/4.26  tff(c_28, plain, (![A_16]: (v1_relat_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.19/4.26  tff(c_13878, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_13862, c_28])).
% 11.19/4.26  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.19/4.26  tff(c_13899, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13869, c_13869, c_42])).
% 11.19/4.26  tff(c_13960, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13906, c_13906, c_13899])).
% 11.19/4.26  tff(c_14568, plain, (![A_545, B_546]: (r1_tarski(k2_relat_1(A_545), k2_relat_1(B_546)) | ~r1_tarski(A_545, B_546) | ~v1_relat_1(B_546) | ~v1_relat_1(A_545))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.19/4.26  tff(c_14582, plain, (![A_545]: (r1_tarski(k2_relat_1(A_545), '#skF_4') | ~r1_tarski(A_545, '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_545))), inference(superposition, [status(thm), theory('equality')], [c_13960, c_14568])).
% 11.19/4.26  tff(c_14978, plain, (![A_568]: (r1_tarski(k2_relat_1(A_568), '#skF_4') | ~r1_tarski(A_568, '#skF_4') | ~v1_relat_1(A_568))), inference(demodulation, [status(thm), theory('equality')], [c_13878, c_14582])).
% 11.19/4.26  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.19/4.26  tff(c_14986, plain, (![A_568]: (k2_relat_1(A_568)='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1(A_568)) | ~r1_tarski(A_568, '#skF_4') | ~v1_relat_1(A_568))), inference(resolution, [status(thm)], [c_14978, c_10])).
% 11.19/4.26  tff(c_15000, plain, (![A_568]: (k2_relat_1(A_568)='#skF_4' | ~r1_tarski(A_568, '#skF_4') | ~v1_relat_1(A_568))), inference(demodulation, [status(thm), theory('equality')], [c_13955, c_14986])).
% 11.19/4.26  tff(c_15334, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_15331, c_15000])).
% 11.19/4.26  tff(c_15345, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_15334])).
% 11.19/4.26  tff(c_15347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13965, c_15345])).
% 11.19/4.26  tff(c_15348, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_194])).
% 11.19/4.26  tff(c_15358, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15348, c_15348, c_44])).
% 11.19/4.26  tff(c_15394, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15358, c_150])).
% 11.19/4.26  tff(c_15576, plain, (![A_600, B_601]: (v1_xboole_0(k1_funct_2(A_600, B_601)) | ~v1_xboole_0(B_601) | v1_xboole_0(A_600))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.19/4.26  tff(c_15587, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_15576, c_149])).
% 11.19/4.26  tff(c_15589, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_15587])).
% 11.19/4.26  tff(c_48, plain, (![A_26]: (k1_relat_1(A_26)!=k1_xboole_0 | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.19/4.26  tff(c_15379, plain, (![A_580]: (k1_relat_1(A_580)!='#skF_5' | A_580='#skF_5' | ~v1_relat_1(A_580))), inference(demodulation, [status(thm), theory('equality')], [c_15348, c_15348, c_48])).
% 11.19/4.26  tff(c_15385, plain, (![A_28]: (k1_relat_1('#skF_2'(A_28))!='#skF_5' | '#skF_2'(A_28)='#skF_5')), inference(resolution, [status(thm)], [c_60, c_15379])).
% 11.19/4.26  tff(c_15391, plain, (![A_28]: (A_28!='#skF_5' | '#skF_2'(A_28)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_15385])).
% 11.19/4.26  tff(c_16285, plain, (![A_670, B_671]: (r1_tarski(k1_relat_1(A_670), k1_relat_1(B_671)) | ~r1_tarski(A_670, B_671) | ~v1_relat_1(B_671) | ~v1_relat_1(A_670))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.19/4.26  tff(c_16299, plain, (![A_670]: (r1_tarski(k1_relat_1(A_670), '#skF_5') | ~r1_tarski(A_670, '#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_670))), inference(superposition, [status(thm), theory('equality')], [c_15358, c_16285])).
% 11.19/4.26  tff(c_16467, plain, (![A_685]: (r1_tarski(k1_relat_1(A_685), '#skF_5') | ~r1_tarski(A_685, '#skF_5') | ~v1_relat_1(A_685))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_16299])).
% 11.19/4.26  tff(c_16490, plain, (![A_28]: (r1_tarski(A_28, '#skF_5') | ~r1_tarski('#skF_2'(A_28), '#skF_5') | ~v1_relat_1('#skF_2'(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_16467])).
% 11.19/4.26  tff(c_16529, plain, (![A_687]: (r1_tarski(A_687, '#skF_5') | ~r1_tarski('#skF_2'(A_687), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_16490])).
% 11.19/4.26  tff(c_16535, plain, (![A_28]: (r1_tarski(A_28, '#skF_5') | ~r1_tarski('#skF_5', '#skF_5') | A_28!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15391, c_16529])).
% 11.19/4.26  tff(c_16540, plain, (![A_688]: (r1_tarski(A_688, '#skF_5') | A_688!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16535])).
% 11.19/4.26  tff(c_15898, plain, (![A_633, C_634, B_635]: (m1_subset_1(A_633, C_634) | ~m1_subset_1(B_635, k1_zfmisc_1(C_634)) | ~r2_hidden(A_633, B_635))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.19/4.26  tff(c_15911, plain, (![A_638, B_639, A_640]: (m1_subset_1(A_638, B_639) | ~r2_hidden(A_638, A_640) | ~r1_tarski(A_640, B_639))), inference(resolution, [status(thm)], [c_24, c_15898])).
% 11.19/4.26  tff(c_15924, plain, (![A_642, B_643]: (m1_subset_1('#skF_1'(A_642), B_643) | ~r1_tarski(A_642, B_643) | v1_xboole_0(A_642))), inference(resolution, [status(thm)], [c_4, c_15911])).
% 11.19/4.26  tff(c_15976, plain, (![A_650, B_651]: (r1_tarski('#skF_1'(A_650), B_651) | ~r1_tarski(A_650, k1_zfmisc_1(B_651)) | v1_xboole_0(A_650))), inference(resolution, [status(thm)], [c_15924, c_22])).
% 11.19/4.26  tff(c_15353, plain, (![A_9]: (A_9='#skF_5' | ~r1_tarski(A_9, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_15348, c_15348, c_18])).
% 11.19/4.26  tff(c_16008, plain, (![A_657]: ('#skF_1'(A_657)='#skF_5' | ~r1_tarski(A_657, k1_zfmisc_1('#skF_5')) | v1_xboole_0(A_657))), inference(resolution, [status(thm)], [c_15976, c_15353])).
% 11.19/4.26  tff(c_16029, plain, ('#skF_1'(k1_zfmisc_1('#skF_5'))='#skF_5' | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_16008])).
% 11.19/4.26  tff(c_16030, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_16029])).
% 11.19/4.26  tff(c_15354, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_15348, c_8])).
% 11.19/4.26  tff(c_16084, plain, (k1_zfmisc_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_16030, c_15354])).
% 11.19/4.26  tff(c_15984, plain, (![A_650]: ('#skF_1'(A_650)='#skF_5' | ~r1_tarski(A_650, k1_zfmisc_1('#skF_5')) | v1_xboole_0(A_650))), inference(resolution, [status(thm)], [c_15976, c_15353])).
% 11.19/4.26  tff(c_16104, plain, (![A_650]: ('#skF_1'(A_650)='#skF_5' | ~r1_tarski(A_650, '#skF_5') | v1_xboole_0(A_650))), inference(demodulation, [status(thm), theory('equality')], [c_16084, c_15984])).
% 11.19/4.26  tff(c_16763, plain, (![A_697]: ('#skF_1'(A_697)='#skF_5' | v1_xboole_0(A_697) | A_697!='#skF_5')), inference(resolution, [status(thm)], [c_16540, c_16104])).
% 11.19/4.26  tff(c_16779, plain, ('#skF_1'('#skF_4')='#skF_5' | '#skF_5'!='#skF_4'), inference(resolution, [status(thm)], [c_16763, c_15589])).
% 11.19/4.26  tff(c_16783, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_16779])).
% 11.19/4.26  tff(c_15627, plain, (![C_608, A_609, B_610]: (v1_funct_2(C_608, A_609, B_610) | ~r2_hidden(C_608, k1_funct_2(A_609, B_610)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.19/4.26  tff(c_15636, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_90, c_15627])).
% 11.19/4.26  tff(c_20, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.19/4.26  tff(c_15355, plain, (![A_10]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_15348, c_20])).
% 11.19/4.26  tff(c_16138, plain, (![A_661, B_662, C_663]: (k1_relset_1(A_661, B_662, C_663)=k1_relat_1(C_663) | ~m1_subset_1(C_663, k1_zfmisc_1(k2_zfmisc_1(A_661, B_662))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.19/4.26  tff(c_16152, plain, (![A_661, B_662]: (k1_relset_1(A_661, B_662, '#skF_5')=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_15355, c_16138])).
% 11.19/4.26  tff(c_16161, plain, (![A_661, B_662]: (k1_relset_1(A_661, B_662, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15358, c_16152])).
% 11.19/4.26  tff(c_74, plain, (![B_38, A_37, C_39]: (k1_xboole_0=B_38 | k1_relset_1(A_37, B_38, C_39)=A_37 | ~v1_funct_2(C_39, A_37, B_38) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.19/4.26  tff(c_17193, plain, (![B_716, A_717, C_718]: (B_716='#skF_5' | k1_relset_1(A_717, B_716, C_718)=A_717 | ~v1_funct_2(C_718, A_717, B_716) | ~m1_subset_1(C_718, k1_zfmisc_1(k2_zfmisc_1(A_717, B_716))))), inference(demodulation, [status(thm), theory('equality')], [c_15348, c_74])).
% 11.19/4.26  tff(c_17207, plain, (![B_716, A_717]: (B_716='#skF_5' | k1_relset_1(A_717, B_716, '#skF_5')=A_717 | ~v1_funct_2('#skF_5', A_717, B_716))), inference(resolution, [status(thm)], [c_15355, c_17193])).
% 11.19/4.26  tff(c_17219, plain, (![B_719, A_720]: (B_719='#skF_5' | A_720='#skF_5' | ~v1_funct_2('#skF_5', A_720, B_719))), inference(demodulation, [status(thm), theory('equality')], [c_16161, c_17207])).
% 11.19/4.26  tff(c_17237, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_15636, c_17219])).
% 11.19/4.26  tff(c_17256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15394, c_16783, c_17237])).
% 11.19/4.26  tff(c_17258, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_16779])).
% 11.19/4.26  tff(c_15360, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15348, c_6])).
% 11.19/4.26  tff(c_17328, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17258, c_15360])).
% 11.19/4.26  tff(c_17334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15589, c_17328])).
% 11.19/4.26  tff(c_17335, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_15587])).
% 11.19/4.26  tff(c_17339, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_17335, c_15354])).
% 11.19/4.26  tff(c_17346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15394, c_17339])).
% 11.19/4.26  tff(c_17348, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_88])).
% 11.19/4.26  tff(c_17414, plain, (![A_732]: (k1_relat_1(A_732)!=k1_xboole_0 | k1_xboole_0=A_732 | ~v1_relat_1(A_732))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.19/4.26  tff(c_17426, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_94, c_17414])).
% 11.19/4.26  tff(c_17435, plain, (k1_xboole_0!='#skF_3' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17348, c_17426])).
% 11.19/4.26  tff(c_17436, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_17435])).
% 11.19/4.26  tff(c_17977, plain, (![A_801, B_802]: (r1_tarski(k1_relat_1(A_801), k1_relat_1(B_802)) | ~r1_tarski(A_801, B_802) | ~v1_relat_1(B_802) | ~v1_relat_1(A_801))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.19/4.26  tff(c_17988, plain, (![B_802]: (r1_tarski('#skF_3', k1_relat_1(B_802)) | ~r1_tarski('#skF_5', B_802) | ~v1_relat_1(B_802) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_17348, c_17977])).
% 11.19/4.26  tff(c_18021, plain, (![B_803]: (r1_tarski('#skF_3', k1_relat_1(B_803)) | ~r1_tarski('#skF_5', B_803) | ~v1_relat_1(B_803))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_17988])).
% 11.19/4.26  tff(c_18035, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_5', k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_18021])).
% 11.19/4.26  tff(c_18044, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_18035])).
% 11.19/4.26  tff(c_18045, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_18044])).
% 11.19/4.26  tff(c_32, plain, (![A_19, B_20]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_19, B_20)), B_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.19/4.26  tff(c_17423, plain, (![A_28]: (k1_relat_1('#skF_2'(A_28))!=k1_xboole_0 | '#skF_2'(A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_17414])).
% 11.19/4.26  tff(c_17433, plain, (![A_28]: (k1_xboole_0!=A_28 | '#skF_2'(A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_17423])).
% 11.19/4.26  tff(c_17997, plain, (![A_801, A_28]: (r1_tarski(k1_relat_1(A_801), A_28) | ~r1_tarski(A_801, '#skF_2'(A_28)) | ~v1_relat_1('#skF_2'(A_28)) | ~v1_relat_1(A_801))), inference(superposition, [status(thm), theory('equality')], [c_56, c_17977])).
% 11.19/4.26  tff(c_18978, plain, (![A_850, A_851]: (r1_tarski(k1_relat_1(A_850), A_851) | ~r1_tarski(A_850, '#skF_2'(A_851)) | ~v1_relat_1(A_850))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_17997])).
% 11.19/4.26  tff(c_19008, plain, (![A_28, A_851]: (r1_tarski(A_28, A_851) | ~r1_tarski('#skF_2'(A_28), '#skF_2'(A_851)) | ~v1_relat_1('#skF_2'(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_18978])).
% 11.19/4.26  tff(c_19065, plain, (![A_855, A_856]: (r1_tarski(A_855, A_856) | ~r1_tarski('#skF_2'(A_855), '#skF_2'(A_856)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_19008])).
% 11.19/4.26  tff(c_19068, plain, (![A_28, A_856]: (r1_tarski(A_28, A_856) | ~r1_tarski(k1_xboole_0, '#skF_2'(A_856)) | k1_xboole_0!=A_28)), inference(superposition, [status(thm), theory('equality')], [c_17433, c_19065])).
% 11.19/4.26  tff(c_19082, plain, (![A_857, A_858]: (r1_tarski(A_857, A_858) | k1_xboole_0!=A_857)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_19068])).
% 11.19/4.26  tff(c_19268, plain, (![A_864, A_863]: (A_864=A_863 | ~r1_tarski(A_863, A_864) | k1_xboole_0!=A_864)), inference(resolution, [status(thm)], [c_19082, c_10])).
% 11.19/4.26  tff(c_19354, plain, (![A_872, B_873]: (k2_relat_1(k2_zfmisc_1(A_872, B_873))=B_873 | k1_xboole_0!=B_873)), inference(resolution, [status(thm)], [c_32, c_19268])).
% 11.19/4.26  tff(c_17382, plain, (![A_728]: (k2_relat_1(A_728)!=k1_xboole_0 | k1_xboole_0=A_728 | ~v1_relat_1(A_728))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.19/4.26  tff(c_17395, plain, (![A_17, B_18]: (k2_relat_1(k2_zfmisc_1(A_17, B_18))!=k1_xboole_0 | k2_zfmisc_1(A_17, B_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_17382])).
% 11.19/4.26  tff(c_19654, plain, (![B_889, A_890]: (k1_xboole_0!=B_889 | k2_zfmisc_1(A_890, B_889)=k1_xboole_0 | k1_xboole_0!=B_889)), inference(superposition, [status(thm), theory('equality')], [c_19354, c_17395])).
% 11.19/4.26  tff(c_19702, plain, (![A_890, B_889]: (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k2_zfmisc_1(A_890, B_889)=k1_xboole_0 | k1_xboole_0!=B_889 | k1_xboole_0!=B_889)), inference(superposition, [status(thm), theory('equality')], [c_19654, c_17395])).
% 11.19/4.26  tff(c_19732, plain, (![A_890, B_889]: (k2_zfmisc_1(A_890, B_889)=k1_xboole_0 | k1_xboole_0!=B_889)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_19702])).
% 11.19/4.26  tff(c_17901, plain, (![C_786, A_787, B_788]: (m1_subset_1(C_786, k1_zfmisc_1(k2_zfmisc_1(A_787, B_788))) | ~r2_hidden(C_786, k1_funct_2(A_787, B_788)))), inference(cnfTransformation, [status(thm)], [f_157])).
% 11.19/4.26  tff(c_20086, plain, (![C_909, A_910, B_911]: (r1_tarski(C_909, k2_zfmisc_1(A_910, B_911)) | ~r2_hidden(C_909, k1_funct_2(A_910, B_911)))), inference(resolution, [status(thm)], [c_17901, c_22])).
% 11.19/4.26  tff(c_20115, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_20086])).
% 11.19/4.26  tff(c_20134, plain, (r1_tarski('#skF_5', k1_xboole_0) | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_19732, c_20115])).
% 11.19/4.26  tff(c_20145, plain, (k1_xboole_0!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_18045, c_20134])).
% 11.19/4.26  tff(c_17347, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_88])).
% 11.19/4.26  tff(c_34, plain, (![A_21, B_22]: (k2_relat_1(k2_zfmisc_1(A_21, B_22))=B_22 | k1_xboole_0=B_22 | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.19/4.26  tff(c_18136, plain, (![A_810, B_811]: (r1_tarski(k2_relat_1(A_810), k2_relat_1(B_811)) | ~r1_tarski(A_810, B_811) | ~v1_relat_1(B_811) | ~v1_relat_1(A_810))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.19/4.26  tff(c_18144, plain, (![A_810, B_22, A_21]: (r1_tarski(k2_relat_1(A_810), B_22) | ~r1_tarski(A_810, k2_zfmisc_1(A_21, B_22)) | ~v1_relat_1(k2_zfmisc_1(A_21, B_22)) | ~v1_relat_1(A_810) | k1_xboole_0=B_22 | k1_xboole_0=A_21)), inference(superposition, [status(thm), theory('equality')], [c_34, c_18136])).
% 11.19/4.26  tff(c_25287, plain, (![A_1053, B_1054, A_1055]: (r1_tarski(k2_relat_1(A_1053), B_1054) | ~r1_tarski(A_1053, k2_zfmisc_1(A_1055, B_1054)) | ~v1_relat_1(A_1053) | k1_xboole_0=B_1054 | k1_xboole_0=A_1055)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_18144])).
% 11.19/4.26  tff(c_25297, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_20115, c_25287])).
% 11.19/4.26  tff(c_25321, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_25297])).
% 11.19/4.26  tff(c_25323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17436, c_20145, c_17347, c_25321])).
% 11.19/4.26  tff(c_25324, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_18044])).
% 11.19/4.26  tff(c_25327, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_25324, c_10])).
% 11.19/4.26  tff(c_25333, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_25327])).
% 11.19/4.26  tff(c_25335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17436, c_25333])).
% 11.19/4.26  tff(c_25337, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_17435])).
% 11.19/4.26  tff(c_25336, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_17435])).
% 11.19/4.26  tff(c_25357, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25337, c_25336])).
% 11.19/4.26  tff(c_25349, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_25336, c_25336, c_42])).
% 11.19/4.26  tff(c_25384, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25357, c_25357, c_25349])).
% 11.19/4.26  tff(c_17401, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_94, c_17382])).
% 11.19/4.26  tff(c_17402, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_17401])).
% 11.19/4.26  tff(c_25339, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_25336, c_17402])).
% 11.19/4.26  tff(c_25362, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25357, c_25357, c_25339])).
% 11.19/4.26  tff(c_25405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25384, c_25362])).
% 11.19/4.26  tff(c_25406, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_17401])).
% 11.19/4.26  tff(c_25416, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_25406, c_25406, c_44])).
% 11.19/4.26  tff(c_25420, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17348, c_25416])).
% 11.19/4.26  tff(c_25415, plain, (![A_8]: (r1_tarski('#skF_5', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_25406, c_16])).
% 11.19/4.26  tff(c_25464, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_25420, c_25415])).
% 11.19/4.26  tff(c_25425, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25420, c_25406])).
% 11.19/4.26  tff(c_25407, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_17401])).
% 11.19/4.26  tff(c_25466, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25425, c_25420, c_25407])).
% 11.19/4.26  tff(c_25426, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25420, c_17347])).
% 11.19/4.26  tff(c_25505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25464, c_25466, c_25426])).
% 11.19/4.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/4.26  
% 11.19/4.26  Inference rules
% 11.19/4.26  ----------------------
% 11.19/4.26  #Ref     : 8
% 11.19/4.26  #Sup     : 5436
% 11.19/4.26  #Fact    : 12
% 11.19/4.26  #Define  : 0
% 11.19/4.26  #Split   : 44
% 11.19/4.26  #Chain   : 0
% 11.19/4.26  #Close   : 0
% 11.19/4.26  
% 11.19/4.26  Ordering : KBO
% 11.19/4.26  
% 11.19/4.26  Simplification rules
% 11.19/4.26  ----------------------
% 11.19/4.26  #Subsume      : 1323
% 11.19/4.26  #Demod        : 3108
% 11.19/4.26  #Tautology    : 2497
% 11.19/4.26  #SimpNegUnit  : 317
% 11.19/4.26  #BackRed      : 411
% 11.19/4.26  
% 11.19/4.26  #Partial instantiations: 0
% 11.19/4.26  #Strategies tried      : 1
% 11.19/4.26  
% 11.19/4.26  Timing (in seconds)
% 11.19/4.26  ----------------------
% 11.19/4.26  Preprocessing        : 0.38
% 11.19/4.26  Parsing              : 0.20
% 11.19/4.26  CNF conversion       : 0.03
% 11.19/4.26  Main loop            : 3.04
% 11.19/4.26  Inferencing          : 0.81
% 11.19/4.26  Reduction            : 0.99
% 11.19/4.26  Demodulation         : 0.68
% 11.19/4.26  BG Simplification    : 0.09
% 11.19/4.26  Subsumption          : 0.94
% 11.19/4.26  Abstraction          : 0.10
% 11.19/4.26  MUC search           : 0.00
% 11.19/4.26  Cooper               : 0.00
% 11.19/4.26  Total                : 3.49
% 11.19/4.26  Index Insertion      : 0.00
% 11.19/4.26  Index Deletion       : 0.00
% 11.19/4.26  Index Matching       : 0.00
% 11.19/4.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
