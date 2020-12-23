%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:41 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 227 expanded)
%              Number of leaves         :   39 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  144 ( 482 expanded)
%              Number of equality atoms :   85 ( 193 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(c_12,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_26,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_171,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_174,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_171])).

tff(c_177,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_174])).

tff(c_36,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) = k1_xboole_0
      | k1_relat_1(A_24) != k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_184,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_177,c_36])).

tff(c_186,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_34,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) = k1_xboole_0
      | k2_relat_1(A_24) != k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_185,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_177,c_34])).

tff(c_196,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_185])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,k1_relat_1(B_23))
      | k11_relat_1(B_23,A_22) = k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_301,plain,(
    ! [B_90,A_91] :
      ( k1_tarski(k1_funct_1(B_90,A_91)) = k11_relat_1(B_90,A_91)
      | ~ r2_hidden(A_91,k1_relat_1(B_90))
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_306,plain,(
    ! [B_92,A_93] :
      ( k1_tarski(k1_funct_1(B_92,A_93)) = k11_relat_1(B_92,A_93)
      | ~ v1_funct_1(B_92)
      | k11_relat_1(B_92,A_93) = k1_xboole_0
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_30,c_301])).

tff(c_280,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_290,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_280])).

tff(c_56,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_291,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_56])).

tff(c_312,plain,
    ( k11_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | k11_relat_1('#skF_3','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_291])).

tff(c_337,plain,
    ( k11_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3')
    | k11_relat_1('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_64,c_312])).

tff(c_339,plain,(
    k11_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_264,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_274,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_264])).

tff(c_347,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_350,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_347])).

tff(c_359,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_274,c_350])).

tff(c_360,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_359])).

tff(c_24,plain,(
    ! [A_16,B_18] :
      ( k9_relat_1(A_16,k1_tarski(B_18)) = k11_relat_1(A_16,B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_470,plain,(
    ! [A_106] :
      ( k9_relat_1(A_106,k1_relat_1('#skF_3')) = k11_relat_1(A_106,'#skF_1')
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_24])).

tff(c_28,plain,(
    ! [A_21] :
      ( k9_relat_1(A_21,k1_relat_1(A_21)) = k2_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_477,plain,
    ( k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_28])).

tff(c_487,plain,(
    k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_177,c_477])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_487])).

tff(c_490,plain,(
    k11_relat_1('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_491,plain,(
    k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_562,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_491])).

tff(c_563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_562])).

tff(c_565,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_677,plain,(
    ! [A_129,B_130,C_131] :
      ( k1_relset_1(A_129,B_130,C_131) = k1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_680,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_677])).

tff(c_688,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_680])).

tff(c_836,plain,(
    ! [B_159,A_160,C_161] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,C_161) = A_160
      | ~ v1_funct_2(C_161,A_160,B_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_839,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_836])).

tff(c_848,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_688,c_839])).

tff(c_849,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_848])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( k2_zfmisc_1(k1_tarski(B_10),A_9) != k1_xboole_0
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_867,plain,(
    ! [A_9] :
      ( k2_zfmisc_1(k1_xboole_0,A_9) != k1_xboole_0
      | k1_xboole_0 = A_9 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_16])).

tff(c_886,plain,(
    ! [A_162] : k1_xboole_0 = A_162 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_867])).

tff(c_564,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_693,plain,(
    ! [A_132,B_133,C_134] :
      ( k2_relset_1(A_132,B_133,C_134) = k2_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_696,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_693])).

tff(c_704,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_696])).

tff(c_705,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_56])).

tff(c_1019,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_886,c_705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:06:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.60  
% 3.10/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.60  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.10/1.60  
% 3.10/1.60  %Foreground sorts:
% 3.10/1.60  
% 3.10/1.60  
% 3.10/1.60  %Background operators:
% 3.10/1.60  
% 3.10/1.60  
% 3.10/1.60  %Foreground operators:
% 3.10/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.10/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.60  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.10/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.10/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.10/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.10/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.60  
% 3.51/1.62  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.51/1.62  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.51/1.62  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.51/1.62  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.51/1.62  tff(f_82, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.51/1.62  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.51/1.62  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 3.51/1.62  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.51/1.62  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.51/1.62  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.51/1.62  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.51/1.62  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.51/1.62  tff(f_46, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 3.51/1.62  tff(c_12, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.51/1.62  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.51/1.62  tff(c_62, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.51/1.62  tff(c_26, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.51/1.62  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.51/1.62  tff(c_171, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.51/1.62  tff(c_174, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_171])).
% 3.51/1.62  tff(c_177, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_174])).
% 3.51/1.62  tff(c_36, plain, (![A_24]: (k2_relat_1(A_24)=k1_xboole_0 | k1_relat_1(A_24)!=k1_xboole_0 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.51/1.62  tff(c_184, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_177, c_36])).
% 3.51/1.62  tff(c_186, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_184])).
% 3.51/1.62  tff(c_34, plain, (![A_24]: (k1_relat_1(A_24)=k1_xboole_0 | k2_relat_1(A_24)!=k1_xboole_0 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.51/1.62  tff(c_185, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_177, c_34])).
% 3.51/1.62  tff(c_196, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_186, c_185])).
% 3.51/1.62  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.51/1.62  tff(c_30, plain, (![A_22, B_23]: (r2_hidden(A_22, k1_relat_1(B_23)) | k11_relat_1(B_23, A_22)=k1_xboole_0 | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.51/1.62  tff(c_301, plain, (![B_90, A_91]: (k1_tarski(k1_funct_1(B_90, A_91))=k11_relat_1(B_90, A_91) | ~r2_hidden(A_91, k1_relat_1(B_90)) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.51/1.62  tff(c_306, plain, (![B_92, A_93]: (k1_tarski(k1_funct_1(B_92, A_93))=k11_relat_1(B_92, A_93) | ~v1_funct_1(B_92) | k11_relat_1(B_92, A_93)=k1_xboole_0 | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_30, c_301])).
% 3.51/1.62  tff(c_280, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.62  tff(c_290, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_280])).
% 3.51/1.62  tff(c_56, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.51/1.62  tff(c_291, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_56])).
% 3.51/1.62  tff(c_312, plain, (k11_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | k11_relat_1('#skF_3', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_306, c_291])).
% 3.51/1.62  tff(c_337, plain, (k11_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3') | k11_relat_1('#skF_3', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_177, c_64, c_312])).
% 3.51/1.62  tff(c_339, plain, (k11_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_337])).
% 3.51/1.62  tff(c_264, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.51/1.62  tff(c_274, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_264])).
% 3.51/1.62  tff(c_347, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.51/1.62  tff(c_350, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_60, c_347])).
% 3.51/1.62  tff(c_359, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_274, c_350])).
% 3.51/1.62  tff(c_360, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_359])).
% 3.51/1.62  tff(c_24, plain, (![A_16, B_18]: (k9_relat_1(A_16, k1_tarski(B_18))=k11_relat_1(A_16, B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.51/1.62  tff(c_470, plain, (![A_106]: (k9_relat_1(A_106, k1_relat_1('#skF_3'))=k11_relat_1(A_106, '#skF_1') | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_360, c_24])).
% 3.51/1.62  tff(c_28, plain, (![A_21]: (k9_relat_1(A_21, k1_relat_1(A_21))=k2_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.51/1.62  tff(c_477, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_470, c_28])).
% 3.51/1.62  tff(c_487, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_177, c_477])).
% 3.51/1.62  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_339, c_487])).
% 3.51/1.62  tff(c_490, plain, (k11_relat_1('#skF_3', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_337])).
% 3.51/1.62  tff(c_491, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_337])).
% 3.51/1.62  tff(c_562, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_490, c_491])).
% 3.51/1.62  tff(c_563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_562])).
% 3.51/1.62  tff(c_565, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_184])).
% 3.51/1.62  tff(c_677, plain, (![A_129, B_130, C_131]: (k1_relset_1(A_129, B_130, C_131)=k1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.51/1.62  tff(c_680, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_677])).
% 3.51/1.62  tff(c_688, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_565, c_680])).
% 3.51/1.62  tff(c_836, plain, (![B_159, A_160, C_161]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, C_161)=A_160 | ~v1_funct_2(C_161, A_160, B_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.51/1.62  tff(c_839, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_60, c_836])).
% 3.51/1.62  tff(c_848, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_688, c_839])).
% 3.51/1.62  tff(c_849, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_848])).
% 3.51/1.62  tff(c_16, plain, (![B_10, A_9]: (k2_zfmisc_1(k1_tarski(B_10), A_9)!=k1_xboole_0 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.51/1.62  tff(c_867, plain, (![A_9]: (k2_zfmisc_1(k1_xboole_0, A_9)!=k1_xboole_0 | k1_xboole_0=A_9)), inference(superposition, [status(thm), theory('equality')], [c_849, c_16])).
% 3.51/1.62  tff(c_886, plain, (![A_162]: (k1_xboole_0=A_162)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_867])).
% 3.51/1.62  tff(c_564, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_184])).
% 3.51/1.62  tff(c_693, plain, (![A_132, B_133, C_134]: (k2_relset_1(A_132, B_133, C_134)=k2_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.51/1.62  tff(c_696, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_693])).
% 3.51/1.62  tff(c_704, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_564, c_696])).
% 3.51/1.62  tff(c_705, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_704, c_56])).
% 3.51/1.62  tff(c_1019, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_886, c_705])).
% 3.51/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.62  
% 3.51/1.62  Inference rules
% 3.51/1.62  ----------------------
% 3.51/1.62  #Ref     : 0
% 3.51/1.62  #Sup     : 249
% 3.51/1.62  #Fact    : 0
% 3.51/1.62  #Define  : 0
% 3.51/1.62  #Split   : 5
% 3.51/1.62  #Chain   : 0
% 3.51/1.62  #Close   : 0
% 3.51/1.62  
% 3.51/1.62  Ordering : KBO
% 3.51/1.62  
% 3.51/1.62  Simplification rules
% 3.51/1.62  ----------------------
% 3.51/1.62  #Subsume      : 39
% 3.51/1.62  #Demod        : 87
% 3.51/1.62  #Tautology    : 97
% 3.51/1.62  #SimpNegUnit  : 19
% 3.51/1.62  #BackRed      : 14
% 3.51/1.62  
% 3.51/1.62  #Partial instantiations: 96
% 3.51/1.62  #Strategies tried      : 1
% 3.51/1.62  
% 3.51/1.62  Timing (in seconds)
% 3.51/1.62  ----------------------
% 3.51/1.62  Preprocessing        : 0.42
% 3.51/1.62  Parsing              : 0.22
% 3.51/1.62  CNF conversion       : 0.02
% 3.51/1.62  Main loop            : 0.38
% 3.51/1.62  Inferencing          : 0.15
% 3.51/1.62  Reduction            : 0.11
% 3.51/1.62  Demodulation         : 0.08
% 3.51/1.62  BG Simplification    : 0.03
% 3.51/1.62  Subsumption          : 0.07
% 3.51/1.62  Abstraction          : 0.02
% 3.51/1.62  MUC search           : 0.00
% 3.51/1.62  Cooper               : 0.00
% 3.51/1.62  Total                : 0.84
% 3.51/1.62  Index Insertion      : 0.00
% 3.51/1.62  Index Deletion       : 0.00
% 3.51/1.62  Index Matching       : 0.00
% 3.51/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
