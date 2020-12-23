%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:13 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 453 expanded)
%              Number of leaves         :   48 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  201 ( 998 expanded)
%              Number of equality atoms :   65 ( 340 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_101,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_139,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1('#skF_1'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_83,plain,(
    ! [A_51] : k2_tarski(A_51,A_51) = k1_tarski(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_8,B_9] : ~ v1_xboole_0(k2_tarski(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [A_51] : ~ v1_xboole_0(k1_tarski(A_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_131,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_139,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_131])).

tff(c_34,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_148,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_139,c_34])).

tff(c_151,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_216,plain,(
    ! [A_80,B_81] :
      ( k9_relat_1(A_80,k1_tarski(B_81)) = k11_relat_1(A_80,B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_187,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_195,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_187])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_199,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_195,c_28])).

tff(c_202,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_199])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_206,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_22])).

tff(c_210,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_206])).

tff(c_222,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_210])).

tff(c_231,plain,(
    k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_222])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,k1_relat_1(B_21))
      | k11_relat_1(B_21,A_20) = k1_xboole_0
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_176,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_184,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_176])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_463,plain,(
    ! [B_118,C_119,A_120] :
      ( r2_hidden(k1_funct_1(B_118,C_119),A_120)
      | ~ r2_hidden(C_119,k1_relat_1(B_118))
      | ~ v1_funct_1(B_118)
      | ~ v5_relat_1(B_118,A_120)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_58,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_477,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_463,c_58])).

tff(c_486,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_184,c_66,c_477])).

tff(c_494,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_486])).

tff(c_503,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_231,c_494])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_503])).

tff(c_506,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_514,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_506,c_32])).

tff(c_36,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_147,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_139,c_36])).

tff(c_149,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_508,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_149])).

tff(c_539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_508])).

tff(c_540,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_550,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_60])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_546,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_4])).

tff(c_541,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_562,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_541])).

tff(c_694,plain,(
    ! [A_148,B_149] :
      ( r2_hidden(A_148,k1_relat_1(B_149))
      | k11_relat_1(B_149,A_148) = '#skF_4'
      | ~ v1_relat_1(B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_24])).

tff(c_700,plain,(
    ! [A_148] :
      ( r2_hidden(A_148,'#skF_4')
      | k11_relat_1('#skF_4',A_148) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_694])).

tff(c_704,plain,(
    ! [A_150] :
      ( r2_hidden(A_150,'#skF_4')
      | k11_relat_1('#skF_4',A_150) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_700])).

tff(c_48,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_707,plain,(
    ! [A_150] :
      ( ~ r1_tarski('#skF_4',A_150)
      | k11_relat_1('#skF_4',A_150) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_704,c_48])).

tff(c_710,plain,(
    ! [A_150] : k11_relat_1('#skF_4',A_150) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_707])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( k11_relat_1(B_21,A_20) != k1_xboole_0
      | ~ r2_hidden(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_721,plain,(
    ! [B_152,A_153] :
      ( k11_relat_1(B_152,A_153) != '#skF_4'
      | ~ r2_hidden(A_153,k1_relat_1(B_152))
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_26])).

tff(c_727,plain,(
    ! [A_153] :
      ( k11_relat_1('#skF_4',A_153) != '#skF_4'
      | ~ r2_hidden(A_153,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_721])).

tff(c_734,plain,(
    ! [A_153] : ~ r2_hidden(A_153,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_710,c_727])).

tff(c_44,plain,(
    ! [A_25,B_28] :
      ( k1_funct_1(A_25,B_28) = k1_xboole_0
      | r2_hidden(B_28,k1_relat_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_737,plain,(
    ! [A_154,B_155] :
      ( k1_funct_1(A_154,B_155) = '#skF_4'
      | r2_hidden(B_155,k1_relat_1(A_154))
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_44])).

tff(c_746,plain,(
    ! [B_155] :
      ( k1_funct_1('#skF_4',B_155) = '#skF_4'
      | r2_hidden(B_155,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_737])).

tff(c_750,plain,(
    ! [B_155] :
      ( k1_funct_1('#skF_4',B_155) = '#skF_4'
      | r2_hidden(B_155,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_66,c_746])).

tff(c_758,plain,(
    ! [B_155] : k1_funct_1('#skF_4',B_155) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_734,c_750])).

tff(c_760,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [D_45,C_44,B_43,A_42] :
      ( r2_hidden(k1_funct_1(D_45,C_44),B_43)
      | k1_xboole_0 = B_43
      | ~ r2_hidden(C_44,A_42)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(D_45,A_42,B_43)
      | ~ v1_funct_1(D_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1045,plain,(
    ! [D_201,C_202,B_203,A_204] :
      ( r2_hidden(k1_funct_1(D_201,C_202),B_203)
      | B_203 = '#skF_4'
      | ~ r2_hidden(C_202,A_204)
      | ~ m1_subset_1(D_201,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_2(D_201,A_204,B_203)
      | ~ v1_funct_1(D_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_56])).

tff(c_1296,plain,(
    ! [D_268,A_269,B_270,B_271] :
      ( r2_hidden(k1_funct_1(D_268,A_269),B_270)
      | B_270 = '#skF_4'
      | ~ m1_subset_1(D_268,k1_zfmisc_1(k2_zfmisc_1(B_271,B_270)))
      | ~ v1_funct_2(D_268,B_271,B_270)
      | ~ v1_funct_1(D_268)
      | v1_xboole_0(B_271)
      | ~ m1_subset_1(A_269,B_271) ) ),
    inference(resolution,[status(thm)],[c_16,c_1045])).

tff(c_1298,plain,(
    ! [A_269] :
      ( r2_hidden(k1_funct_1('#skF_4',A_269),'#skF_3')
      | '#skF_3' = '#skF_4'
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(k1_tarski('#skF_2'))
      | ~ m1_subset_1(A_269,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_62,c_1296])).

tff(c_1304,plain,(
    ! [A_269] :
      ( r2_hidden('#skF_4','#skF_3')
      | '#skF_3' = '#skF_4'
      | v1_xboole_0(k1_tarski('#skF_2'))
      | ~ m1_subset_1(A_269,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_758,c_1298])).

tff(c_1313,plain,(
    ! [A_275] : ~ m1_subset_1(A_275,k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_550,c_760,c_1304])).

tff(c_1318,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_1313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.75  
% 3.70/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.70/1.75  
% 3.70/1.75  %Foreground sorts:
% 3.70/1.75  
% 3.70/1.75  
% 3.70/1.75  %Background operators:
% 3.70/1.75  
% 3.70/1.75  
% 3.70/1.75  %Foreground operators:
% 3.70/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.70/1.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.70/1.75  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.70/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.70/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.70/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.70/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.70/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.70/1.75  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.70/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.70/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.70/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.70/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.70/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.70/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.70/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.70/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.75  
% 4.07/1.77  tff(f_40, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.07/1.77  tff(f_30, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.07/1.77  tff(f_37, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 4.07/1.77  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 4.07/1.77  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.07/1.77  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.07/1.77  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 4.07/1.77  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.07/1.77  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.07/1.77  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.07/1.77  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 4.07/1.77  tff(f_112, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 4.07/1.77  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.07/1.77  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.07/1.77  tff(f_117, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.07/1.77  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 4.07/1.77  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.07/1.77  tff(f_139, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 4.07/1.77  tff(c_14, plain, (![A_10]: (m1_subset_1('#skF_1'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.07/1.77  tff(c_83, plain, (![A_51]: (k2_tarski(A_51, A_51)=k1_tarski(A_51))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.07/1.77  tff(c_12, plain, (![A_8, B_9]: (~v1_xboole_0(k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.07/1.77  tff(c_88, plain, (![A_51]: (~v1_xboole_0(k1_tarski(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_12])).
% 4.07/1.77  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.07/1.77  tff(c_131, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.07/1.77  tff(c_139, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_131])).
% 4.07/1.77  tff(c_34, plain, (![A_24]: (k2_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.07/1.77  tff(c_148, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_139, c_34])).
% 4.07/1.77  tff(c_151, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_148])).
% 4.07/1.77  tff(c_216, plain, (![A_80, B_81]: (k9_relat_1(A_80, k1_tarski(B_81))=k11_relat_1(A_80, B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.07/1.77  tff(c_187, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.07/1.77  tff(c_195, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_62, c_187])).
% 4.07/1.77  tff(c_28, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.07/1.77  tff(c_199, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_195, c_28])).
% 4.07/1.77  tff(c_202, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_199])).
% 4.07/1.77  tff(c_22, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.07/1.77  tff(c_206, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_202, c_22])).
% 4.07/1.77  tff(c_210, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_206])).
% 4.07/1.77  tff(c_222, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_216, c_210])).
% 4.07/1.77  tff(c_231, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_222])).
% 4.07/1.77  tff(c_24, plain, (![A_20, B_21]: (r2_hidden(A_20, k1_relat_1(B_21)) | k11_relat_1(B_21, A_20)=k1_xboole_0 | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.07/1.77  tff(c_176, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.07/1.77  tff(c_184, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_176])).
% 4.07/1.77  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.07/1.77  tff(c_463, plain, (![B_118, C_119, A_120]: (r2_hidden(k1_funct_1(B_118, C_119), A_120) | ~r2_hidden(C_119, k1_relat_1(B_118)) | ~v1_funct_1(B_118) | ~v5_relat_1(B_118, A_120) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.07/1.77  tff(c_58, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.07/1.77  tff(c_477, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_463, c_58])).
% 4.07/1.77  tff(c_486, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_184, c_66, c_477])).
% 4.07/1.77  tff(c_494, plain, (k11_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_486])).
% 4.07/1.77  tff(c_503, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_139, c_231, c_494])).
% 4.07/1.77  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_503])).
% 4.07/1.77  tff(c_506, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_148])).
% 4.07/1.77  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.07/1.77  tff(c_514, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_506, c_506, c_32])).
% 4.07/1.77  tff(c_36, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.07/1.77  tff(c_147, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_139, c_36])).
% 4.07/1.77  tff(c_149, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_147])).
% 4.07/1.77  tff(c_508, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_506, c_149])).
% 4.07/1.77  tff(c_539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_508])).
% 4.07/1.77  tff(c_540, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_147])).
% 4.07/1.77  tff(c_60, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.07/1.77  tff(c_550, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_540, c_60])).
% 4.07/1.77  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.07/1.77  tff(c_546, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_4])).
% 4.07/1.77  tff(c_541, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_147])).
% 4.07/1.77  tff(c_562, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_540, c_541])).
% 4.07/1.77  tff(c_694, plain, (![A_148, B_149]: (r2_hidden(A_148, k1_relat_1(B_149)) | k11_relat_1(B_149, A_148)='#skF_4' | ~v1_relat_1(B_149))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_24])).
% 4.07/1.77  tff(c_700, plain, (![A_148]: (r2_hidden(A_148, '#skF_4') | k11_relat_1('#skF_4', A_148)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_562, c_694])).
% 4.07/1.77  tff(c_704, plain, (![A_150]: (r2_hidden(A_150, '#skF_4') | k11_relat_1('#skF_4', A_150)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_700])).
% 4.07/1.77  tff(c_48, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.07/1.77  tff(c_707, plain, (![A_150]: (~r1_tarski('#skF_4', A_150) | k11_relat_1('#skF_4', A_150)='#skF_4')), inference(resolution, [status(thm)], [c_704, c_48])).
% 4.07/1.77  tff(c_710, plain, (![A_150]: (k11_relat_1('#skF_4', A_150)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_707])).
% 4.07/1.77  tff(c_26, plain, (![B_21, A_20]: (k11_relat_1(B_21, A_20)!=k1_xboole_0 | ~r2_hidden(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.07/1.77  tff(c_721, plain, (![B_152, A_153]: (k11_relat_1(B_152, A_153)!='#skF_4' | ~r2_hidden(A_153, k1_relat_1(B_152)) | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_26])).
% 4.07/1.77  tff(c_727, plain, (![A_153]: (k11_relat_1('#skF_4', A_153)!='#skF_4' | ~r2_hidden(A_153, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_562, c_721])).
% 4.07/1.77  tff(c_734, plain, (![A_153]: (~r2_hidden(A_153, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_710, c_727])).
% 4.07/1.77  tff(c_44, plain, (![A_25, B_28]: (k1_funct_1(A_25, B_28)=k1_xboole_0 | r2_hidden(B_28, k1_relat_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.07/1.77  tff(c_737, plain, (![A_154, B_155]: (k1_funct_1(A_154, B_155)='#skF_4' | r2_hidden(B_155, k1_relat_1(A_154)) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_44])).
% 4.07/1.77  tff(c_746, plain, (![B_155]: (k1_funct_1('#skF_4', B_155)='#skF_4' | r2_hidden(B_155, '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_562, c_737])).
% 4.07/1.77  tff(c_750, plain, (![B_155]: (k1_funct_1('#skF_4', B_155)='#skF_4' | r2_hidden(B_155, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_66, c_746])).
% 4.07/1.77  tff(c_758, plain, (![B_155]: (k1_funct_1('#skF_4', B_155)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_734, c_750])).
% 4.07/1.77  tff(c_760, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_758, c_58])).
% 4.07/1.77  tff(c_64, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.07/1.77  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.07/1.77  tff(c_56, plain, (![D_45, C_44, B_43, A_42]: (r2_hidden(k1_funct_1(D_45, C_44), B_43) | k1_xboole_0=B_43 | ~r2_hidden(C_44, A_42) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(D_45, A_42, B_43) | ~v1_funct_1(D_45))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.07/1.77  tff(c_1045, plain, (![D_201, C_202, B_203, A_204]: (r2_hidden(k1_funct_1(D_201, C_202), B_203) | B_203='#skF_4' | ~r2_hidden(C_202, A_204) | ~m1_subset_1(D_201, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_2(D_201, A_204, B_203) | ~v1_funct_1(D_201))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_56])).
% 4.07/1.77  tff(c_1296, plain, (![D_268, A_269, B_270, B_271]: (r2_hidden(k1_funct_1(D_268, A_269), B_270) | B_270='#skF_4' | ~m1_subset_1(D_268, k1_zfmisc_1(k2_zfmisc_1(B_271, B_270))) | ~v1_funct_2(D_268, B_271, B_270) | ~v1_funct_1(D_268) | v1_xboole_0(B_271) | ~m1_subset_1(A_269, B_271))), inference(resolution, [status(thm)], [c_16, c_1045])).
% 4.07/1.77  tff(c_1298, plain, (![A_269]: (r2_hidden(k1_funct_1('#skF_4', A_269), '#skF_3') | '#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0(k1_tarski('#skF_2')) | ~m1_subset_1(A_269, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_62, c_1296])).
% 4.07/1.77  tff(c_1304, plain, (![A_269]: (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | v1_xboole_0(k1_tarski('#skF_2')) | ~m1_subset_1(A_269, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_758, c_1298])).
% 4.07/1.77  tff(c_1313, plain, (![A_275]: (~m1_subset_1(A_275, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_88, c_550, c_760, c_1304])).
% 4.07/1.77  tff(c_1318, plain, $false, inference(resolution, [status(thm)], [c_14, c_1313])).
% 4.07/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.77  
% 4.07/1.77  Inference rules
% 4.07/1.77  ----------------------
% 4.07/1.77  #Ref     : 0
% 4.07/1.77  #Sup     : 252
% 4.07/1.77  #Fact    : 0
% 4.07/1.77  #Define  : 0
% 4.07/1.77  #Split   : 5
% 4.07/1.77  #Chain   : 0
% 4.07/1.77  #Close   : 0
% 4.07/1.77  
% 4.07/1.77  Ordering : KBO
% 4.07/1.77  
% 4.07/1.77  Simplification rules
% 4.07/1.77  ----------------------
% 4.07/1.77  #Subsume      : 34
% 4.07/1.77  #Demod        : 319
% 4.07/1.77  #Tautology    : 112
% 4.07/1.77  #SimpNegUnit  : 5
% 4.07/1.77  #BackRed      : 20
% 4.07/1.77  
% 4.07/1.77  #Partial instantiations: 0
% 4.07/1.77  #Strategies tried      : 1
% 4.07/1.77  
% 4.07/1.77  Timing (in seconds)
% 4.07/1.77  ----------------------
% 4.07/1.77  Preprocessing        : 0.41
% 4.07/1.77  Parsing              : 0.23
% 4.07/1.77  CNF conversion       : 0.03
% 4.07/1.77  Main loop            : 0.50
% 4.07/1.77  Inferencing          : 0.18
% 4.07/1.77  Reduction            : 0.16
% 4.07/1.77  Demodulation         : 0.11
% 4.07/1.77  BG Simplification    : 0.03
% 4.07/1.77  Subsumption          : 0.09
% 4.07/1.77  Abstraction          : 0.02
% 4.07/1.77  MUC search           : 0.00
% 4.07/1.77  Cooper               : 0.00
% 4.07/1.77  Total                : 0.95
% 4.07/1.77  Index Insertion      : 0.00
% 4.07/1.77  Index Deletion       : 0.00
% 4.07/1.77  Index Matching       : 0.00
% 4.07/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
