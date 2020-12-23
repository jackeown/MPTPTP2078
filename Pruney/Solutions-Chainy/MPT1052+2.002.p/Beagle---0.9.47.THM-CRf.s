%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:08 EST 2020

% Result     : Theorem 11.21s
% Output     : CNFRefutation 11.46s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 902 expanded)
%              Number of leaves         :   45 ( 305 expanded)
%              Depth                    :   14
%              Number of atoms          :  362 (2037 expanded)
%              Number of equality atoms :  153 ( 572 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
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

tff(f_60,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_78,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_203,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_392,plain,(
    ! [A_92,B_93] :
      ( v1_xboole_0(k1_funct_2(A_92,B_93))
      | ~ v1_xboole_0(B_93)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_80,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_139,plain,(
    ! [B_51,A_52] :
      ( ~ r2_hidden(B_51,A_52)
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_139])).

tff(c_412,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_392,c_143])).

tff(c_449,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_84,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_988,plain,(
    ! [C_134,A_135,B_136] :
      ( m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ r2_hidden(C_134,k1_funct_2(A_135,B_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1630,plain,(
    ! [C_170,A_171,B_172] :
      ( r1_tarski(C_170,k2_zfmisc_1(A_171,B_172))
      | ~ r2_hidden(C_170,k1_funct_2(A_171,B_172)) ) ),
    inference(resolution,[status(thm)],[c_988,c_32])).

tff(c_1672,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_1630])).

tff(c_40,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( k2_relat_1(k2_zfmisc_1(A_24,B_25)) = B_25
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1076,plain,(
    ! [A_143,B_144] :
      ( r1_tarski(k2_relat_1(A_143),k2_relat_1(B_144))
      | ~ r1_tarski(A_143,B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1085,plain,(
    ! [A_143,B_25,A_24] :
      ( r1_tarski(k2_relat_1(A_143),B_25)
      | ~ r1_tarski(A_143,k2_zfmisc_1(A_24,B_25))
      | ~ v1_relat_1(k2_zfmisc_1(A_24,B_25))
      | ~ v1_relat_1(A_143)
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1076])).

tff(c_7267,plain,(
    ! [A_348,B_349,A_350] :
      ( r1_tarski(k2_relat_1(A_348),B_349)
      | ~ r1_tarski(A_348,k2_zfmisc_1(A_350,B_349))
      | ~ v1_relat_1(A_348)
      | k1_xboole_0 = B_349
      | k1_xboole_0 = A_350 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1085])).

tff(c_7271,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1672,c_7267])).

tff(c_7285,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7271])).

tff(c_7291,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7285])).

tff(c_313,plain,(
    ! [A_82] :
      ( k2_relat_1(A_82) = k1_xboole_0
      | k1_relat_1(A_82) != k1_xboole_0
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_331,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_313])).

tff(c_347,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_371,plain,(
    ! [A_91] :
      ( k1_relat_1(A_91) = k1_xboole_0
      | k2_relat_1(A_91) != k1_xboole_0
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_383,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_371])).

tff(c_391,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_347,c_383])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_244,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2'(A_73,B_74),B_74)
      | r1_xboole_0(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_254,plain,(
    ! [B_75,A_76] :
      ( ~ v1_xboole_0(B_75)
      | r1_xboole_0(A_76,B_75) ) ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_259,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = A_77
      | ~ v1_xboole_0(B_78) ) ),
    inference(resolution,[status(thm)],[c_254,c_22])).

tff(c_265,plain,(
    ! [A_77] : k4_xboole_0(A_77,k1_xboole_0) = A_77 ),
    inference(resolution,[status(thm)],[c_6,c_259])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_97,plain,(
    ! [A_47] : k2_zfmisc_1(A_47,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_40])).

tff(c_130,plain,(
    ! [A_50] :
      ( v1_xboole_0(k1_relat_1(A_50))
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_150,plain,(
    ! [A_55] :
      ( k1_relat_1(A_55) = k1_xboole_0
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_130,c_8])).

tff(c_158,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_319,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_313])).

tff(c_329,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_319])).

tff(c_1091,plain,(
    ! [A_143] :
      ( r1_tarski(k2_relat_1(A_143),k1_xboole_0)
      | ~ r1_tarski(A_143,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_1076])).

tff(c_1131,plain,(
    ! [A_149] :
      ( r1_tarski(k2_relat_1(A_149),k1_xboole_0)
      | ~ r1_tarski(A_149,k1_xboole_0)
      | ~ v1_relat_1(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1091])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1134,plain,(
    ! [A_149] :
      ( k4_xboole_0(k2_relat_1(A_149),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_149,k1_xboole_0)
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_1131,c_18])).

tff(c_1147,plain,(
    ! [A_150] :
      ( k2_relat_1(A_150) = k1_xboole_0
      | ~ r1_tarski(A_150,k1_xboole_0)
      | ~ v1_relat_1(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_1134])).

tff(c_1160,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) = k1_xboole_0
      | ~ v1_relat_1(A_11)
      | k4_xboole_0(A_11,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_1147])).

tff(c_1174,plain,(
    ! [A_151] :
      ( k2_relat_1(A_151) = k1_xboole_0
      | ~ v1_relat_1(A_151)
      | k1_xboole_0 != A_151 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_1160])).

tff(c_1192,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_84,c_1174])).

tff(c_1201,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_1192])).

tff(c_7375,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7291,c_1201])).

tff(c_30,plain,(
    ! [B_17] : k2_zfmisc_1(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7416,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_3',B_17) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7291,c_7291,c_30])).

tff(c_1676,plain,(
    k4_xboole_0('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1672,c_18])).

tff(c_7364,plain,(
    k4_xboole_0('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7291,c_1676])).

tff(c_7703,plain,(
    k4_xboole_0('#skF_5','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7416,c_7364])).

tff(c_7409,plain,(
    ! [A_77] : k4_xboole_0(A_77,'#skF_3') = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7291,c_265])).

tff(c_7788,plain,(
    '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7703,c_7409])).

tff(c_7795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7375,c_7788])).

tff(c_7797,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7285])).

tff(c_44,plain,(
    ! [A_24,B_25] :
      ( k1_relat_1(k2_zfmisc_1(A_24,B_25)) = A_24
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1202,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(k1_relat_1(A_152),k1_relat_1(B_153))
      | ~ r1_tarski(A_152,B_153)
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1217,plain,(
    ! [A_152,A_24,B_25] :
      ( r1_tarski(k1_relat_1(A_152),A_24)
      | ~ r1_tarski(A_152,k2_zfmisc_1(A_24,B_25))
      | ~ v1_relat_1(k2_zfmisc_1(A_24,B_25))
      | ~ v1_relat_1(A_152)
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1202])).

tff(c_8082,plain,(
    ! [A_375,A_376,B_377] :
      ( r1_tarski(k1_relat_1(A_375),A_376)
      | ~ r1_tarski(A_375,k2_zfmisc_1(A_376,B_377))
      | ~ v1_relat_1(A_375)
      | k1_xboole_0 = B_377
      | k1_xboole_0 = A_376 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1217])).

tff(c_8086,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1672,c_8082])).

tff(c_8100,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_8086])).

tff(c_8101,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_7797,c_8100])).

tff(c_8107,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8101])).

tff(c_8245,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8107,c_6])).

tff(c_8247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_8245])).

tff(c_8249,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8101])).

tff(c_818,plain,(
    ! [C_118,A_119,B_120] :
      ( v1_funct_2(C_118,A_119,B_120)
      | ~ r2_hidden(C_118,k1_funct_2(A_119,B_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_849,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_818])).

tff(c_70,plain,(
    ! [C_40,A_38,B_39] :
      ( m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ r2_hidden(C_40,k1_funct_2(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1823,plain,(
    ! [A_174,B_175,C_176] :
      ( k1_relset_1(A_174,B_175,C_176) = k1_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3768,plain,(
    ! [A_245,B_246,C_247] :
      ( k1_relset_1(A_245,B_246,C_247) = k1_relat_1(C_247)
      | ~ r2_hidden(C_247,k1_funct_2(A_245,B_246)) ) ),
    inference(resolution,[status(thm)],[c_70,c_1823])).

tff(c_3841,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_3768])).

tff(c_2393,plain,(
    ! [B_221,A_222,C_223] :
      ( k1_xboole_0 = B_221
      | k1_relset_1(A_222,B_221,C_223) = A_222
      | ~ v1_funct_2(C_223,A_222,B_221)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_222,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8472,plain,(
    ! [B_380,A_381,C_382] :
      ( k1_xboole_0 = B_380
      | k1_relset_1(A_381,B_380,C_382) = A_381
      | ~ v1_funct_2(C_382,A_381,B_380)
      | ~ r2_hidden(C_382,k1_funct_2(A_381,B_380)) ) ),
    inference(resolution,[status(thm)],[c_70,c_2393])).

tff(c_8553,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_8472])).

tff(c_8574,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_3841,c_8553])).

tff(c_8576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_8249,c_8574])).

tff(c_8578,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_8614,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8578,c_8])).

tff(c_8577,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_8596,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8577,c_8])).

tff(c_8649,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8614,c_8596])).

tff(c_8627,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8596,c_8596,c_329])).

tff(c_8702,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8649,c_8649,c_8627])).

tff(c_8658,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8649,c_80])).

tff(c_28,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8639,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8596,c_8596,c_28])).

tff(c_8807,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8649,c_8649,c_8639])).

tff(c_9054,plain,(
    ! [C_411,A_412,B_413] :
      ( m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413)))
      | ~ r2_hidden(C_411,k1_funct_2(A_412,B_413)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_9527,plain,(
    ! [C_443,A_444] :
      ( m1_subset_1(C_443,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(C_443,k1_funct_2(A_444,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8807,c_9054])).

tff(c_9549,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8658,c_9527])).

tff(c_9556,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_9549,c_32])).

tff(c_8633,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = '#skF_3'
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8596,c_18])).

tff(c_8906,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = '#skF_4'
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8649,c_8633])).

tff(c_9560,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9556,c_8906])).

tff(c_8630,plain,(
    ! [A_77] : k4_xboole_0(A_77,'#skF_3') = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8596,c_265])).

tff(c_8724,plain,(
    ! [A_77] : k4_xboole_0(A_77,'#skF_4') = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8649,c_8630])).

tff(c_9570,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9560,c_8724])).

tff(c_8624,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8596,c_391])).

tff(c_8723,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8649,c_8624])).

tff(c_9587,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9570,c_8723])).

tff(c_9597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8702,c_9587])).

tff(c_9599,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_9604,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9599,c_203])).

tff(c_9635,plain,(
    ! [A_447,B_448] :
      ( v1_xboole_0(k1_funct_2(A_447,B_448))
      | ~ v1_xboole_0(B_448)
      | v1_xboole_0(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_9652,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_9635,c_143])).

tff(c_9655,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_9652])).

tff(c_10099,plain,(
    ! [C_478,A_479,B_480] :
      ( v1_funct_2(C_478,A_479,B_480)
      | ~ r2_hidden(C_478,k1_funct_2(A_479,B_480)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_10130,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_10099])).

tff(c_10315,plain,(
    ! [C_498,A_499,B_500] :
      ( m1_subset_1(C_498,k1_zfmisc_1(k2_zfmisc_1(A_499,B_500)))
      | ~ r2_hidden(C_498,k1_funct_2(A_499,B_500)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_10466,plain,(
    ! [C_516,A_517,B_518] :
      ( r1_tarski(C_516,k2_zfmisc_1(A_517,B_518))
      | ~ r2_hidden(C_516,k1_funct_2(A_517,B_518)) ) ),
    inference(resolution,[status(thm)],[c_10315,c_32])).

tff(c_10504,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_10466])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10433,plain,(
    ! [A_511,B_512,C_513] :
      ( k1_relset_1(A_511,B_512,C_513) = k1_relat_1(C_513)
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_13324,plain,(
    ! [A_618,B_619,A_620] :
      ( k1_relset_1(A_618,B_619,A_620) = k1_relat_1(A_620)
      | ~ r1_tarski(A_620,k2_zfmisc_1(A_618,B_619)) ) ),
    inference(resolution,[status(thm)],[c_34,c_10433])).

tff(c_13327,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10504,c_13324])).

tff(c_13343,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9599,c_13327])).

tff(c_11853,plain,(
    ! [B_588,A_589,C_590] :
      ( k1_xboole_0 = B_588
      | k1_relset_1(A_589,B_588,C_590) = A_589
      | ~ v1_funct_2(C_590,A_589,B_588)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(A_589,B_588))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_17783,plain,(
    ! [B_772,A_773,C_774] :
      ( k1_xboole_0 = B_772
      | k1_relset_1(A_773,B_772,C_774) = A_773
      | ~ v1_funct_2(C_774,A_773,B_772)
      | ~ r2_hidden(C_774,k1_funct_2(A_773,B_772)) ) ),
    inference(resolution,[status(thm)],[c_70,c_11853])).

tff(c_17855,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_17783])).

tff(c_17873,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10130,c_13343,c_17855])).

tff(c_17874,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_9604,c_17873])).

tff(c_18030,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17874,c_6])).

tff(c_18032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9655,c_18030])).

tff(c_18033,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_9652])).

tff(c_18045,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18033,c_8])).

tff(c_18052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9604,c_18045])).

tff(c_18054,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_18162,plain,(
    ! [A_803] :
      ( k2_relat_1(A_803) = k1_xboole_0
      | k1_relat_1(A_803) != k1_xboole_0
      | ~ v1_relat_1(A_803) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_18174,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_18162])).

tff(c_18181,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18054,c_18174])).

tff(c_18186,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18181])).

tff(c_18265,plain,(
    ! [A_810,B_811] :
      ( v1_xboole_0(k1_funct_2(A_810,B_811))
      | ~ v1_xboole_0(B_811)
      | v1_xboole_0(A_810) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_18285,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18265,c_143])).

tff(c_18288,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18285])).

tff(c_18053,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_18913,plain,(
    ! [C_850,A_851,B_852] :
      ( m1_subset_1(C_850,k1_zfmisc_1(k2_zfmisc_1(A_851,B_852)))
      | ~ r2_hidden(C_850,k1_funct_2(A_851,B_852)) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_19714,plain,(
    ! [C_895,A_896,B_897] :
      ( r1_tarski(C_895,k2_zfmisc_1(A_896,B_897))
      | ~ r2_hidden(C_895,k1_funct_2(A_896,B_897)) ) ),
    inference(resolution,[status(thm)],[c_18913,c_32])).

tff(c_19760,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_19714])).

tff(c_19116,plain,(
    ! [A_870,B_871] :
      ( r1_tarski(k2_relat_1(A_870),k2_relat_1(B_871))
      | ~ r1_tarski(A_870,B_871)
      | ~ v1_relat_1(B_871)
      | ~ v1_relat_1(A_870) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_19125,plain,(
    ! [A_870,B_25,A_24] :
      ( r1_tarski(k2_relat_1(A_870),B_25)
      | ~ r1_tarski(A_870,k2_zfmisc_1(A_24,B_25))
      | ~ v1_relat_1(k2_zfmisc_1(A_24,B_25))
      | ~ v1_relat_1(A_870)
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_19116])).

tff(c_26619,plain,(
    ! [A_1069,B_1070,A_1071] :
      ( r1_tarski(k2_relat_1(A_1069),B_1070)
      | ~ r1_tarski(A_1069,k2_zfmisc_1(A_1071,B_1070))
      | ~ v1_relat_1(A_1069)
      | k1_xboole_0 = B_1070
      | k1_xboole_0 = A_1071 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_19125])).

tff(c_26623,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_19760,c_26619])).

tff(c_26638,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_26623])).

tff(c_26639,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_18186,c_18053,c_26638])).

tff(c_26807,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26639,c_6])).

tff(c_26809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18288,c_26807])).

tff(c_26810,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_18285])).

tff(c_26824,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26810,c_8])).

tff(c_26832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18186,c_26824])).

tff(c_26834,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18181])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26849,plain,(
    ! [A_13] : r1_tarski('#skF_3',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26834,c_20])).

tff(c_26833,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18181])).

tff(c_26855,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26834,c_26833])).

tff(c_26856,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26855,c_18053])).

tff(c_26871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26849,c_26856])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:39:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.21/4.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.35/4.55  
% 11.35/4.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.35/4.55  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 11.35/4.55  
% 11.35/4.55  %Foreground sorts:
% 11.35/4.55  
% 11.35/4.55  
% 11.35/4.55  %Background operators:
% 11.35/4.55  
% 11.35/4.55  
% 11.35/4.55  %Foreground operators:
% 11.35/4.55  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 11.35/4.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.35/4.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.35/4.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.35/4.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.35/4.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.35/4.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.35/4.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.35/4.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.35/4.55  tff('#skF_5', type, '#skF_5': $i).
% 11.35/4.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.35/4.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.35/4.55  tff('#skF_3', type, '#skF_3': $i).
% 11.35/4.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.35/4.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.35/4.55  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 11.35/4.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.35/4.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.35/4.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.35/4.55  tff('#skF_4', type, '#skF_4': $i).
% 11.35/4.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.35/4.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.35/4.55  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 11.35/4.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.35/4.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.35/4.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.35/4.55  
% 11.46/4.58  tff(f_163, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_2)).
% 11.46/4.58  tff(f_142, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 11.46/4.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.46/4.58  tff(f_150, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 11.46/4.58  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.46/4.58  tff(f_84, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.46/4.58  tff(f_96, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 11.46/4.58  tff(f_107, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 11.46/4.58  tff(f_113, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 11.46/4.58  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.46/4.58  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.46/4.58  tff(f_64, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.46/4.58  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.46/4.58  tff(f_70, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.46/4.58  tff(f_82, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 11.46/4.58  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.46/4.58  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.46/4.58  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.46/4.58  tff(f_60, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.46/4.58  tff(c_78, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.46/4.58  tff(c_203, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_78])).
% 11.46/4.58  tff(c_392, plain, (![A_92, B_93]: (v1_xboole_0(k1_funct_2(A_92, B_93)) | ~v1_xboole_0(B_93) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.46/4.58  tff(c_80, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.46/4.58  tff(c_139, plain, (![B_51, A_52]: (~r2_hidden(B_51, A_52) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.46/4.58  tff(c_143, plain, (~v1_xboole_0(k1_funct_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_139])).
% 11.46/4.58  tff(c_412, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_392, c_143])).
% 11.46/4.58  tff(c_449, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_412])).
% 11.46/4.58  tff(c_84, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.46/4.58  tff(c_988, plain, (![C_134, A_135, B_136]: (m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~r2_hidden(C_134, k1_funct_2(A_135, B_136)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 11.46/4.58  tff(c_32, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.46/4.58  tff(c_1630, plain, (![C_170, A_171, B_172]: (r1_tarski(C_170, k2_zfmisc_1(A_171, B_172)) | ~r2_hidden(C_170, k1_funct_2(A_171, B_172)))), inference(resolution, [status(thm)], [c_988, c_32])).
% 11.46/4.58  tff(c_1672, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_1630])).
% 11.46/4.58  tff(c_40, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.46/4.58  tff(c_42, plain, (![A_24, B_25]: (k2_relat_1(k2_zfmisc_1(A_24, B_25))=B_25 | k1_xboole_0=B_25 | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.46/4.58  tff(c_1076, plain, (![A_143, B_144]: (r1_tarski(k2_relat_1(A_143), k2_relat_1(B_144)) | ~r1_tarski(A_143, B_144) | ~v1_relat_1(B_144) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.46/4.58  tff(c_1085, plain, (![A_143, B_25, A_24]: (r1_tarski(k2_relat_1(A_143), B_25) | ~r1_tarski(A_143, k2_zfmisc_1(A_24, B_25)) | ~v1_relat_1(k2_zfmisc_1(A_24, B_25)) | ~v1_relat_1(A_143) | k1_xboole_0=B_25 | k1_xboole_0=A_24)), inference(superposition, [status(thm), theory('equality')], [c_42, c_1076])).
% 11.46/4.58  tff(c_7267, plain, (![A_348, B_349, A_350]: (r1_tarski(k2_relat_1(A_348), B_349) | ~r1_tarski(A_348, k2_zfmisc_1(A_350, B_349)) | ~v1_relat_1(A_348) | k1_xboole_0=B_349 | k1_xboole_0=A_350)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1085])).
% 11.46/4.58  tff(c_7271, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1672, c_7267])).
% 11.46/4.58  tff(c_7285, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7271])).
% 11.46/4.58  tff(c_7291, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_7285])).
% 11.46/4.58  tff(c_313, plain, (![A_82]: (k2_relat_1(A_82)=k1_xboole_0 | k1_relat_1(A_82)!=k1_xboole_0 | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.46/4.58  tff(c_331, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_313])).
% 11.46/4.58  tff(c_347, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_331])).
% 11.46/4.58  tff(c_371, plain, (![A_91]: (k1_relat_1(A_91)=k1_xboole_0 | k2_relat_1(A_91)!=k1_xboole_0 | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.46/4.58  tff(c_383, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_371])).
% 11.46/4.58  tff(c_391, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_347, c_383])).
% 11.46/4.58  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.46/4.58  tff(c_244, plain, (![A_73, B_74]: (r2_hidden('#skF_2'(A_73, B_74), B_74) | r1_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.46/4.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.46/4.58  tff(c_254, plain, (![B_75, A_76]: (~v1_xboole_0(B_75) | r1_xboole_0(A_76, B_75))), inference(resolution, [status(thm)], [c_244, c_2])).
% 11.46/4.58  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.46/4.58  tff(c_259, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=A_77 | ~v1_xboole_0(B_78))), inference(resolution, [status(thm)], [c_254, c_22])).
% 11.46/4.58  tff(c_265, plain, (![A_77]: (k4_xboole_0(A_77, k1_xboole_0)=A_77)), inference(resolution, [status(thm)], [c_6, c_259])).
% 11.46/4.58  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.46/4.58  tff(c_97, plain, (![A_47]: (k2_zfmisc_1(A_47, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.46/4.58  tff(c_101, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_97, c_40])).
% 11.46/4.58  tff(c_130, plain, (![A_50]: (v1_xboole_0(k1_relat_1(A_50)) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.46/4.58  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.46/4.58  tff(c_150, plain, (![A_55]: (k1_relat_1(A_55)=k1_xboole_0 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_130, c_8])).
% 11.46/4.58  tff(c_158, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_150])).
% 11.46/4.58  tff(c_319, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_101, c_313])).
% 11.46/4.58  tff(c_329, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_158, c_319])).
% 11.46/4.58  tff(c_1091, plain, (![A_143]: (r1_tarski(k2_relat_1(A_143), k1_xboole_0) | ~r1_tarski(A_143, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_143))), inference(superposition, [status(thm), theory('equality')], [c_329, c_1076])).
% 11.46/4.58  tff(c_1131, plain, (![A_149]: (r1_tarski(k2_relat_1(A_149), k1_xboole_0) | ~r1_tarski(A_149, k1_xboole_0) | ~v1_relat_1(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_1091])).
% 11.46/4.58  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.46/4.58  tff(c_1134, plain, (![A_149]: (k4_xboole_0(k2_relat_1(A_149), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_149, k1_xboole_0) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_1131, c_18])).
% 11.46/4.58  tff(c_1147, plain, (![A_150]: (k2_relat_1(A_150)=k1_xboole_0 | ~r1_tarski(A_150, k1_xboole_0) | ~v1_relat_1(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_1134])).
% 11.46/4.58  tff(c_1160, plain, (![A_11]: (k2_relat_1(A_11)=k1_xboole_0 | ~v1_relat_1(A_11) | k4_xboole_0(A_11, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1147])).
% 11.46/4.58  tff(c_1174, plain, (![A_151]: (k2_relat_1(A_151)=k1_xboole_0 | ~v1_relat_1(A_151) | k1_xboole_0!=A_151)), inference(demodulation, [status(thm), theory('equality')], [c_265, c_1160])).
% 11.46/4.58  tff(c_1192, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_84, c_1174])).
% 11.46/4.58  tff(c_1201, plain, (k1_xboole_0!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_391, c_1192])).
% 11.46/4.58  tff(c_7375, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7291, c_1201])).
% 11.46/4.58  tff(c_30, plain, (![B_17]: (k2_zfmisc_1(k1_xboole_0, B_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.46/4.58  tff(c_7416, plain, (![B_17]: (k2_zfmisc_1('#skF_3', B_17)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7291, c_7291, c_30])).
% 11.46/4.58  tff(c_1676, plain, (k4_xboole_0('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1672, c_18])).
% 11.46/4.58  tff(c_7364, plain, (k4_xboole_0('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7291, c_1676])).
% 11.46/4.58  tff(c_7703, plain, (k4_xboole_0('#skF_5', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7416, c_7364])).
% 11.46/4.58  tff(c_7409, plain, (![A_77]: (k4_xboole_0(A_77, '#skF_3')=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_7291, c_265])).
% 11.46/4.58  tff(c_7788, plain, ('#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7703, c_7409])).
% 11.46/4.58  tff(c_7795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7375, c_7788])).
% 11.46/4.58  tff(c_7797, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_7285])).
% 11.46/4.58  tff(c_44, plain, (![A_24, B_25]: (k1_relat_1(k2_zfmisc_1(A_24, B_25))=A_24 | k1_xboole_0=B_25 | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.46/4.58  tff(c_1202, plain, (![A_152, B_153]: (r1_tarski(k1_relat_1(A_152), k1_relat_1(B_153)) | ~r1_tarski(A_152, B_153) | ~v1_relat_1(B_153) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.46/4.58  tff(c_1217, plain, (![A_152, A_24, B_25]: (r1_tarski(k1_relat_1(A_152), A_24) | ~r1_tarski(A_152, k2_zfmisc_1(A_24, B_25)) | ~v1_relat_1(k2_zfmisc_1(A_24, B_25)) | ~v1_relat_1(A_152) | k1_xboole_0=B_25 | k1_xboole_0=A_24)), inference(superposition, [status(thm), theory('equality')], [c_44, c_1202])).
% 11.46/4.58  tff(c_8082, plain, (![A_375, A_376, B_377]: (r1_tarski(k1_relat_1(A_375), A_376) | ~r1_tarski(A_375, k2_zfmisc_1(A_376, B_377)) | ~v1_relat_1(A_375) | k1_xboole_0=B_377 | k1_xboole_0=A_376)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1217])).
% 11.46/4.58  tff(c_8086, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1672, c_8082])).
% 11.46/4.58  tff(c_8100, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_8086])).
% 11.46/4.58  tff(c_8101, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_7797, c_8100])).
% 11.46/4.58  tff(c_8107, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_8101])).
% 11.46/4.58  tff(c_8245, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8107, c_6])).
% 11.46/4.58  tff(c_8247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_449, c_8245])).
% 11.46/4.58  tff(c_8249, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_8101])).
% 11.46/4.58  tff(c_818, plain, (![C_118, A_119, B_120]: (v1_funct_2(C_118, A_119, B_120) | ~r2_hidden(C_118, k1_funct_2(A_119, B_120)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 11.46/4.58  tff(c_849, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_818])).
% 11.46/4.58  tff(c_70, plain, (![C_40, A_38, B_39]: (m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~r2_hidden(C_40, k1_funct_2(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 11.46/4.58  tff(c_1823, plain, (![A_174, B_175, C_176]: (k1_relset_1(A_174, B_175, C_176)=k1_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.46/4.58  tff(c_3768, plain, (![A_245, B_246, C_247]: (k1_relset_1(A_245, B_246, C_247)=k1_relat_1(C_247) | ~r2_hidden(C_247, k1_funct_2(A_245, B_246)))), inference(resolution, [status(thm)], [c_70, c_1823])).
% 11.46/4.58  tff(c_3841, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_80, c_3768])).
% 11.46/4.58  tff(c_2393, plain, (![B_221, A_222, C_223]: (k1_xboole_0=B_221 | k1_relset_1(A_222, B_221, C_223)=A_222 | ~v1_funct_2(C_223, A_222, B_221) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_222, B_221))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.46/4.58  tff(c_8472, plain, (![B_380, A_381, C_382]: (k1_xboole_0=B_380 | k1_relset_1(A_381, B_380, C_382)=A_381 | ~v1_funct_2(C_382, A_381, B_380) | ~r2_hidden(C_382, k1_funct_2(A_381, B_380)))), inference(resolution, [status(thm)], [c_70, c_2393])).
% 11.46/4.58  tff(c_8553, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_8472])).
% 11.46/4.58  tff(c_8574, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_849, c_3841, c_8553])).
% 11.46/4.58  tff(c_8576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_203, c_8249, c_8574])).
% 11.46/4.58  tff(c_8578, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_412])).
% 11.46/4.58  tff(c_8614, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8578, c_8])).
% 11.46/4.58  tff(c_8577, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_412])).
% 11.46/4.58  tff(c_8596, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8577, c_8])).
% 11.46/4.58  tff(c_8649, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8614, c_8596])).
% 11.46/4.58  tff(c_8627, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8596, c_8596, c_329])).
% 11.46/4.58  tff(c_8702, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8649, c_8649, c_8627])).
% 11.46/4.58  tff(c_8658, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8649, c_80])).
% 11.46/4.58  tff(c_28, plain, (![A_16]: (k2_zfmisc_1(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.46/4.58  tff(c_8639, plain, (![A_16]: (k2_zfmisc_1(A_16, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8596, c_8596, c_28])).
% 11.46/4.58  tff(c_8807, plain, (![A_16]: (k2_zfmisc_1(A_16, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8649, c_8649, c_8639])).
% 11.46/4.58  tff(c_9054, plain, (![C_411, A_412, B_413]: (m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))) | ~r2_hidden(C_411, k1_funct_2(A_412, B_413)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 11.46/4.58  tff(c_9527, plain, (![C_443, A_444]: (m1_subset_1(C_443, k1_zfmisc_1('#skF_4')) | ~r2_hidden(C_443, k1_funct_2(A_444, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_8807, c_9054])).
% 11.46/4.58  tff(c_9549, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_8658, c_9527])).
% 11.46/4.58  tff(c_9556, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_9549, c_32])).
% 11.46/4.58  tff(c_8633, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)='#skF_3' | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_8596, c_18])).
% 11.46/4.58  tff(c_8906, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)='#skF_4' | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_8649, c_8633])).
% 11.46/4.58  tff(c_9560, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_9556, c_8906])).
% 11.46/4.58  tff(c_8630, plain, (![A_77]: (k4_xboole_0(A_77, '#skF_3')=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_8596, c_265])).
% 11.46/4.58  tff(c_8724, plain, (![A_77]: (k4_xboole_0(A_77, '#skF_4')=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_8649, c_8630])).
% 11.46/4.58  tff(c_9570, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_9560, c_8724])).
% 11.46/4.58  tff(c_8624, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8596, c_391])).
% 11.46/4.58  tff(c_8723, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8649, c_8624])).
% 11.46/4.58  tff(c_9587, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9570, c_8723])).
% 11.46/4.58  tff(c_9597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8702, c_9587])).
% 11.46/4.58  tff(c_9599, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_331])).
% 11.46/4.58  tff(c_9604, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9599, c_203])).
% 11.46/4.58  tff(c_9635, plain, (![A_447, B_448]: (v1_xboole_0(k1_funct_2(A_447, B_448)) | ~v1_xboole_0(B_448) | v1_xboole_0(A_447))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.46/4.58  tff(c_9652, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_9635, c_143])).
% 11.46/4.58  tff(c_9655, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_9652])).
% 11.46/4.58  tff(c_10099, plain, (![C_478, A_479, B_480]: (v1_funct_2(C_478, A_479, B_480) | ~r2_hidden(C_478, k1_funct_2(A_479, B_480)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 11.46/4.58  tff(c_10130, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_10099])).
% 11.46/4.58  tff(c_10315, plain, (![C_498, A_499, B_500]: (m1_subset_1(C_498, k1_zfmisc_1(k2_zfmisc_1(A_499, B_500))) | ~r2_hidden(C_498, k1_funct_2(A_499, B_500)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 11.46/4.58  tff(c_10466, plain, (![C_516, A_517, B_518]: (r1_tarski(C_516, k2_zfmisc_1(A_517, B_518)) | ~r2_hidden(C_516, k1_funct_2(A_517, B_518)))), inference(resolution, [status(thm)], [c_10315, c_32])).
% 11.46/4.58  tff(c_10504, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_10466])).
% 11.46/4.58  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.46/4.58  tff(c_10433, plain, (![A_511, B_512, C_513]: (k1_relset_1(A_511, B_512, C_513)=k1_relat_1(C_513) | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.46/4.58  tff(c_13324, plain, (![A_618, B_619, A_620]: (k1_relset_1(A_618, B_619, A_620)=k1_relat_1(A_620) | ~r1_tarski(A_620, k2_zfmisc_1(A_618, B_619)))), inference(resolution, [status(thm)], [c_34, c_10433])).
% 11.46/4.58  tff(c_13327, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10504, c_13324])).
% 11.46/4.58  tff(c_13343, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9599, c_13327])).
% 11.46/4.58  tff(c_11853, plain, (![B_588, A_589, C_590]: (k1_xboole_0=B_588 | k1_relset_1(A_589, B_588, C_590)=A_589 | ~v1_funct_2(C_590, A_589, B_588) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(A_589, B_588))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 11.46/4.58  tff(c_17783, plain, (![B_772, A_773, C_774]: (k1_xboole_0=B_772 | k1_relset_1(A_773, B_772, C_774)=A_773 | ~v1_funct_2(C_774, A_773, B_772) | ~r2_hidden(C_774, k1_funct_2(A_773, B_772)))), inference(resolution, [status(thm)], [c_70, c_11853])).
% 11.46/4.58  tff(c_17855, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_17783])).
% 11.46/4.58  tff(c_17873, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10130, c_13343, c_17855])).
% 11.46/4.58  tff(c_17874, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_9604, c_17873])).
% 11.46/4.58  tff(c_18030, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17874, c_6])).
% 11.46/4.58  tff(c_18032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9655, c_18030])).
% 11.46/4.58  tff(c_18033, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_9652])).
% 11.46/4.58  tff(c_18045, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_18033, c_8])).
% 11.46/4.58  tff(c_18052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9604, c_18045])).
% 11.46/4.58  tff(c_18054, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_78])).
% 11.46/4.58  tff(c_18162, plain, (![A_803]: (k2_relat_1(A_803)=k1_xboole_0 | k1_relat_1(A_803)!=k1_xboole_0 | ~v1_relat_1(A_803))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.46/4.58  tff(c_18174, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_18162])).
% 11.46/4.58  tff(c_18181, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18054, c_18174])).
% 11.46/4.58  tff(c_18186, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_18181])).
% 11.46/4.58  tff(c_18265, plain, (![A_810, B_811]: (v1_xboole_0(k1_funct_2(A_810, B_811)) | ~v1_xboole_0(B_811) | v1_xboole_0(A_810))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.46/4.58  tff(c_18285, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_18265, c_143])).
% 11.46/4.58  tff(c_18288, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_18285])).
% 11.46/4.58  tff(c_18053, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_78])).
% 11.46/4.58  tff(c_18913, plain, (![C_850, A_851, B_852]: (m1_subset_1(C_850, k1_zfmisc_1(k2_zfmisc_1(A_851, B_852))) | ~r2_hidden(C_850, k1_funct_2(A_851, B_852)))), inference(cnfTransformation, [status(thm)], [f_150])).
% 11.46/4.58  tff(c_19714, plain, (![C_895, A_896, B_897]: (r1_tarski(C_895, k2_zfmisc_1(A_896, B_897)) | ~r2_hidden(C_895, k1_funct_2(A_896, B_897)))), inference(resolution, [status(thm)], [c_18913, c_32])).
% 11.46/4.58  tff(c_19760, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_19714])).
% 11.46/4.58  tff(c_19116, plain, (![A_870, B_871]: (r1_tarski(k2_relat_1(A_870), k2_relat_1(B_871)) | ~r1_tarski(A_870, B_871) | ~v1_relat_1(B_871) | ~v1_relat_1(A_870))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.46/4.58  tff(c_19125, plain, (![A_870, B_25, A_24]: (r1_tarski(k2_relat_1(A_870), B_25) | ~r1_tarski(A_870, k2_zfmisc_1(A_24, B_25)) | ~v1_relat_1(k2_zfmisc_1(A_24, B_25)) | ~v1_relat_1(A_870) | k1_xboole_0=B_25 | k1_xboole_0=A_24)), inference(superposition, [status(thm), theory('equality')], [c_42, c_19116])).
% 11.46/4.58  tff(c_26619, plain, (![A_1069, B_1070, A_1071]: (r1_tarski(k2_relat_1(A_1069), B_1070) | ~r1_tarski(A_1069, k2_zfmisc_1(A_1071, B_1070)) | ~v1_relat_1(A_1069) | k1_xboole_0=B_1070 | k1_xboole_0=A_1071)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_19125])).
% 11.46/4.58  tff(c_26623, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_19760, c_26619])).
% 11.46/4.58  tff(c_26638, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_26623])).
% 11.46/4.58  tff(c_26639, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_18186, c_18053, c_26638])).
% 11.46/4.58  tff(c_26807, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26639, c_6])).
% 11.46/4.58  tff(c_26809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18288, c_26807])).
% 11.46/4.58  tff(c_26810, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_18285])).
% 11.46/4.58  tff(c_26824, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_26810, c_8])).
% 11.46/4.58  tff(c_26832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18186, c_26824])).
% 11.46/4.58  tff(c_26834, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_18181])).
% 11.46/4.58  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.46/4.58  tff(c_26849, plain, (![A_13]: (r1_tarski('#skF_3', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_26834, c_20])).
% 11.46/4.58  tff(c_26833, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_18181])).
% 11.46/4.58  tff(c_26855, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26834, c_26833])).
% 11.46/4.58  tff(c_26856, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26855, c_18053])).
% 11.46/4.58  tff(c_26871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26849, c_26856])).
% 11.46/4.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.46/4.58  
% 11.46/4.58  Inference rules
% 11.46/4.58  ----------------------
% 11.46/4.58  #Ref     : 0
% 11.46/4.58  #Sup     : 5994
% 11.46/4.58  #Fact    : 12
% 11.46/4.58  #Define  : 0
% 11.46/4.58  #Split   : 29
% 11.46/4.58  #Chain   : 0
% 11.46/4.58  #Close   : 0
% 11.46/4.58  
% 11.46/4.58  Ordering : KBO
% 11.46/4.58  
% 11.46/4.58  Simplification rules
% 11.46/4.58  ----------------------
% 11.46/4.58  #Subsume      : 1330
% 11.46/4.58  #Demod        : 4773
% 11.46/4.58  #Tautology    : 3142
% 11.46/4.58  #SimpNegUnit  : 316
% 11.46/4.58  #BackRed      : 655
% 11.46/4.58  
% 11.46/4.58  #Partial instantiations: 0
% 11.46/4.58  #Strategies tried      : 1
% 11.46/4.58  
% 11.46/4.58  Timing (in seconds)
% 11.46/4.58  ----------------------
% 11.46/4.59  Preprocessing        : 0.38
% 11.46/4.59  Parsing              : 0.20
% 11.46/4.59  CNF conversion       : 0.03
% 11.46/4.59  Main loop            : 3.43
% 11.46/4.59  Inferencing          : 0.99
% 11.46/4.59  Reduction            : 1.10
% 11.46/4.59  Demodulation         : 0.75
% 11.46/4.59  BG Simplification    : 0.11
% 11.46/4.59  Subsumption          : 0.98
% 11.46/4.59  Abstraction          : 0.12
% 11.46/4.59  MUC search           : 0.00
% 11.46/4.59  Cooper               : 0.00
% 11.46/4.59  Total                : 3.87
% 11.46/4.59  Index Insertion      : 0.00
% 11.46/4.59  Index Deletion       : 0.00
% 11.46/4.59  Index Matching       : 0.00
% 11.46/4.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
