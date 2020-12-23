%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:51 EST 2020

% Result     : Theorem 9.08s
% Output     : CNFRefutation 9.08s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 400 expanded)
%              Number of leaves         :   41 ( 144 expanded)
%              Depth                    :   10
%              Number of atoms          :  171 (1301 expanded)
%              Number of equality atoms :   32 ( 369 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_99,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_82,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1712,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( r2_relset_1(A_188,B_189,C_190,C_190)
      | ~ m1_subset_1(D_191,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1812,plain,(
    ! [C_192] :
      ( r2_relset_1('#skF_5','#skF_6',C_192,C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_82,c_1712])).

tff(c_1859,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_1812])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_80,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_78,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1113,plain,(
    ! [C_172,A_173,B_174] :
      ( v1_partfun1(C_172,A_173)
      | ~ v1_funct_2(C_172,A_173,B_174)
      | ~ v1_funct_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | v1_xboole_0(B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1153,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_8')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_1113])).

tff(c_1187,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1153])).

tff(c_1194,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1187])).

tff(c_120,plain,(
    ! [A_66] :
      ( r2_hidden('#skF_4'(A_66),A_66)
      | k1_xboole_0 = A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(A_66)
      | k1_xboole_0 = A_66 ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_1203,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1194,c_124])).

tff(c_1209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1203])).

tff(c_1211,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_86,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_84,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1156,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_1113])).

tff(c_1190,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_1156])).

tff(c_1212,plain,(
    v1_partfun1('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1211,c_1190])).

tff(c_1210,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_74,plain,(
    r1_partfun1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1909,plain,(
    ! [D_195,C_196,A_197,B_198] :
      ( D_195 = C_196
      | ~ r1_partfun1(C_196,D_195)
      | ~ v1_partfun1(D_195,A_197)
      | ~ v1_partfun1(C_196,A_197)
      | ~ m1_subset_1(D_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1(D_195)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1(C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1911,plain,(
    ! [A_197,B_198] :
      ( '#skF_7' = '#skF_8'
      | ~ v1_partfun1('#skF_8',A_197)
      | ~ v1_partfun1('#skF_7',A_197)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_74,c_1909])).

tff(c_1914,plain,(
    ! [A_197,B_198] :
      ( '#skF_7' = '#skF_8'
      | ~ v1_partfun1('#skF_8',A_197)
      | ~ v1_partfun1('#skF_7',A_197)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_80,c_1911])).

tff(c_11120,plain,(
    ! [A_535,B_536] :
      ( ~ v1_partfun1('#skF_8',A_535)
      | ~ v1_partfun1('#skF_7',A_535)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_535,B_536)))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_535,B_536))) ) ),
    inference(splitLeft,[status(thm)],[c_1914])).

tff(c_11148,plain,
    ( ~ v1_partfun1('#skF_8','#skF_5')
    | ~ v1_partfun1('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_82,c_11120])).

tff(c_11173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1212,c_1210,c_11148])).

tff(c_11174,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1914])).

tff(c_70,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_11199,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11174,c_70])).

tff(c_11217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1859,c_11199])).

tff(c_11219,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_11218,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_11225,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11219,c_11218])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11220,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11218,c_12])).

tff(c_11235,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11225,c_11220])).

tff(c_18,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11236,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_6',B_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11219,c_11219,c_18])).

tff(c_11265,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11236,c_11225,c_76])).

tff(c_11288,plain,(
    ! [A_548,B_549] :
      ( r1_tarski(A_548,B_549)
      | ~ m1_subset_1(A_548,k1_zfmisc_1(B_549)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11303,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_11265,c_11288])).

tff(c_40,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_4'(A_34),A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_11268,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_4'(A_34),A_34)
      | A_34 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11219,c_40])).

tff(c_11389,plain,(
    ! [C_569,B_570,A_571] :
      ( r2_hidden(C_569,B_570)
      | ~ r2_hidden(C_569,A_571)
      | ~ r1_tarski(A_571,B_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11474,plain,(
    ! [A_580,B_581] :
      ( r2_hidden('#skF_4'(A_580),B_581)
      | ~ r1_tarski(A_580,B_581)
      | A_580 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_11268,c_11389])).

tff(c_11482,plain,(
    ! [B_582,A_583] :
      ( ~ v1_xboole_0(B_582)
      | ~ r1_tarski(A_583,B_582)
      | A_583 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_11474,c_2])).

tff(c_11497,plain,
    ( ~ v1_xboole_0('#skF_6')
    | '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_11303,c_11482])).

tff(c_11508,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11235,c_11497])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_11262,plain,(
    ! [A_12] : m1_subset_1('#skF_6',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11219,c_20])).

tff(c_11543,plain,(
    ! [A_12] : m1_subset_1('#skF_8',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11508,c_11262])).

tff(c_24,plain,(
    ! [A_13] : m1_subset_1('#skF_3'(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12510,plain,(
    ! [A_666,B_667,C_668,D_669] :
      ( r2_relset_1(A_666,B_667,C_668,C_668)
      | ~ m1_subset_1(D_669,k1_zfmisc_1(k2_zfmisc_1(A_666,B_667)))
      | ~ m1_subset_1(C_668,k1_zfmisc_1(k2_zfmisc_1(A_666,B_667))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_13443,plain,(
    ! [A_719,B_720,C_721] :
      ( r2_relset_1(A_719,B_720,C_721,C_721)
      | ~ m1_subset_1(C_721,k1_zfmisc_1(k2_zfmisc_1(A_719,B_720))) ) ),
    inference(resolution,[status(thm)],[c_24,c_12510])).

tff(c_13490,plain,(
    ! [A_719,B_720] : r2_relset_1(A_719,B_720,'#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_11543,c_13443])).

tff(c_11287,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11236,c_11225,c_82])).

tff(c_11301,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_11287,c_11288])).

tff(c_11500,plain,
    ( ~ v1_xboole_0('#skF_6')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_11301,c_11482])).

tff(c_11511,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11235,c_11500])).

tff(c_11557,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11508,c_11511])).

tff(c_11264,plain,(
    ~ r2_relset_1('#skF_6','#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11225,c_70])).

tff(c_11542,plain,(
    ~ r2_relset_1('#skF_8','#skF_8','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11508,c_11508,c_11264])).

tff(c_11693,plain,(
    ~ r2_relset_1('#skF_8','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11557,c_11542])).

tff(c_13495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13490,c_11693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.08/3.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.08/3.29  
% 9.08/3.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.08/3.29  %$ r2_relset_1 > v1_funct_2 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2
% 9.08/3.29  
% 9.08/3.29  %Foreground sorts:
% 9.08/3.29  
% 9.08/3.29  
% 9.08/3.29  %Background operators:
% 9.08/3.29  
% 9.08/3.29  
% 9.08/3.29  %Foreground operators:
% 9.08/3.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.08/3.29  tff('#skF_4', type, '#skF_4': $i > $i).
% 9.08/3.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.08/3.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.08/3.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.08/3.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 9.08/3.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.08/3.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.08/3.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.08/3.29  tff('#skF_7', type, '#skF_7': $i).
% 9.08/3.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.08/3.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.08/3.29  tff('#skF_5', type, '#skF_5': $i).
% 9.08/3.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.08/3.29  tff('#skF_6', type, '#skF_6': $i).
% 9.08/3.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.08/3.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.08/3.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.08/3.29  tff('#skF_8', type, '#skF_8': $i).
% 9.08/3.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.08/3.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.08/3.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.08/3.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.08/3.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.08/3.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.08/3.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.08/3.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.08/3.29  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 9.08/3.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.08/3.29  
% 9.08/3.31  tff(f_181, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 9.08/3.31  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 9.08/3.31  tff(f_113, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 9.08/3.31  tff(f_99, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 9.08/3.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.08/3.31  tff(f_148, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 9.08/3.31  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.08/3.31  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.08/3.31  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.08/3.31  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.08/3.31  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.08/3.31  tff(f_53, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 9.08/3.31  tff(c_76, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.08/3.31  tff(c_82, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.08/3.31  tff(c_1712, plain, (![A_188, B_189, C_190, D_191]: (r2_relset_1(A_188, B_189, C_190, C_190) | ~m1_subset_1(D_191, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.08/3.31  tff(c_1812, plain, (![C_192]: (r2_relset_1('#skF_5', '#skF_6', C_192, C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_82, c_1712])).
% 9.08/3.31  tff(c_1859, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_76, c_1812])).
% 9.08/3.31  tff(c_72, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.08/3.31  tff(c_92, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_72])).
% 9.08/3.31  tff(c_80, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.08/3.31  tff(c_78, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.08/3.31  tff(c_1113, plain, (![C_172, A_173, B_174]: (v1_partfun1(C_172, A_173) | ~v1_funct_2(C_172, A_173, B_174) | ~v1_funct_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | v1_xboole_0(B_174))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.08/3.31  tff(c_1153, plain, (v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_8') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_76, c_1113])).
% 9.08/3.31  tff(c_1187, plain, (v1_partfun1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1153])).
% 9.08/3.31  tff(c_1194, plain, (v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1187])).
% 9.08/3.31  tff(c_120, plain, (![A_66]: (r2_hidden('#skF_4'(A_66), A_66) | k1_xboole_0=A_66)), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.08/3.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.08/3.31  tff(c_124, plain, (![A_66]: (~v1_xboole_0(A_66) | k1_xboole_0=A_66)), inference(resolution, [status(thm)], [c_120, c_2])).
% 9.08/3.31  tff(c_1203, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1194, c_124])).
% 9.08/3.31  tff(c_1209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1203])).
% 9.08/3.31  tff(c_1211, plain, (~v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_1187])).
% 9.08/3.31  tff(c_86, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.08/3.31  tff(c_84, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.08/3.31  tff(c_1156, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_82, c_1113])).
% 9.08/3.31  tff(c_1190, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_1156])).
% 9.08/3.31  tff(c_1212, plain, (v1_partfun1('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1211, c_1190])).
% 9.08/3.31  tff(c_1210, plain, (v1_partfun1('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_1187])).
% 9.08/3.31  tff(c_74, plain, (r1_partfun1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.08/3.31  tff(c_1909, plain, (![D_195, C_196, A_197, B_198]: (D_195=C_196 | ~r1_partfun1(C_196, D_195) | ~v1_partfun1(D_195, A_197) | ~v1_partfun1(C_196, A_197) | ~m1_subset_1(D_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1(D_195) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1(C_196))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.08/3.31  tff(c_1911, plain, (![A_197, B_198]: ('#skF_7'='#skF_8' | ~v1_partfun1('#skF_8', A_197) | ~v1_partfun1('#skF_7', A_197) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_74, c_1909])).
% 9.08/3.31  tff(c_1914, plain, (![A_197, B_198]: ('#skF_7'='#skF_8' | ~v1_partfun1('#skF_8', A_197) | ~v1_partfun1('#skF_7', A_197) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_80, c_1911])).
% 9.08/3.31  tff(c_11120, plain, (![A_535, B_536]: (~v1_partfun1('#skF_8', A_535) | ~v1_partfun1('#skF_7', A_535) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_535, B_536))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(A_535, B_536))))), inference(splitLeft, [status(thm)], [c_1914])).
% 9.08/3.31  tff(c_11148, plain, (~v1_partfun1('#skF_8', '#skF_5') | ~v1_partfun1('#skF_7', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_82, c_11120])).
% 9.08/3.31  tff(c_11173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1212, c_1210, c_11148])).
% 9.08/3.31  tff(c_11174, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_1914])).
% 9.08/3.31  tff(c_70, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.08/3.31  tff(c_11199, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11174, c_70])).
% 9.08/3.31  tff(c_11217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1859, c_11199])).
% 9.08/3.31  tff(c_11219, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_72])).
% 9.08/3.31  tff(c_11218, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_72])).
% 9.08/3.31  tff(c_11225, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11219, c_11218])).
% 9.08/3.31  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.08/3.31  tff(c_11220, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11218, c_12])).
% 9.08/3.31  tff(c_11235, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11225, c_11220])).
% 9.08/3.31  tff(c_18, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.08/3.31  tff(c_11236, plain, (![B_11]: (k2_zfmisc_1('#skF_6', B_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11219, c_11219, c_18])).
% 9.08/3.31  tff(c_11265, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_11236, c_11225, c_76])).
% 9.08/3.31  tff(c_11288, plain, (![A_548, B_549]: (r1_tarski(A_548, B_549) | ~m1_subset_1(A_548, k1_zfmisc_1(B_549)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.08/3.31  tff(c_11303, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_11265, c_11288])).
% 9.08/3.31  tff(c_40, plain, (![A_34]: (r2_hidden('#skF_4'(A_34), A_34) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.08/3.31  tff(c_11268, plain, (![A_34]: (r2_hidden('#skF_4'(A_34), A_34) | A_34='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11219, c_40])).
% 9.08/3.31  tff(c_11389, plain, (![C_569, B_570, A_571]: (r2_hidden(C_569, B_570) | ~r2_hidden(C_569, A_571) | ~r1_tarski(A_571, B_570))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.08/3.31  tff(c_11474, plain, (![A_580, B_581]: (r2_hidden('#skF_4'(A_580), B_581) | ~r1_tarski(A_580, B_581) | A_580='#skF_6')), inference(resolution, [status(thm)], [c_11268, c_11389])).
% 9.08/3.31  tff(c_11482, plain, (![B_582, A_583]: (~v1_xboole_0(B_582) | ~r1_tarski(A_583, B_582) | A_583='#skF_6')), inference(resolution, [status(thm)], [c_11474, c_2])).
% 9.08/3.31  tff(c_11497, plain, (~v1_xboole_0('#skF_6') | '#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_11303, c_11482])).
% 9.08/3.31  tff(c_11508, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11235, c_11497])).
% 9.08/3.31  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.08/3.31  tff(c_11262, plain, (![A_12]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_11219, c_20])).
% 9.08/3.31  tff(c_11543, plain, (![A_12]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_11508, c_11262])).
% 9.08/3.31  tff(c_24, plain, (![A_13]: (m1_subset_1('#skF_3'(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.08/3.31  tff(c_12510, plain, (![A_666, B_667, C_668, D_669]: (r2_relset_1(A_666, B_667, C_668, C_668) | ~m1_subset_1(D_669, k1_zfmisc_1(k2_zfmisc_1(A_666, B_667))) | ~m1_subset_1(C_668, k1_zfmisc_1(k2_zfmisc_1(A_666, B_667))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.08/3.31  tff(c_13443, plain, (![A_719, B_720, C_721]: (r2_relset_1(A_719, B_720, C_721, C_721) | ~m1_subset_1(C_721, k1_zfmisc_1(k2_zfmisc_1(A_719, B_720))))), inference(resolution, [status(thm)], [c_24, c_12510])).
% 9.08/3.31  tff(c_13490, plain, (![A_719, B_720]: (r2_relset_1(A_719, B_720, '#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_11543, c_13443])).
% 9.08/3.31  tff(c_11287, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_11236, c_11225, c_82])).
% 9.08/3.31  tff(c_11301, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_11287, c_11288])).
% 9.08/3.31  tff(c_11500, plain, (~v1_xboole_0('#skF_6') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_11301, c_11482])).
% 9.08/3.31  tff(c_11511, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11235, c_11500])).
% 9.08/3.31  tff(c_11557, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11508, c_11511])).
% 9.08/3.31  tff(c_11264, plain, (~r2_relset_1('#skF_6', '#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11225, c_70])).
% 9.08/3.31  tff(c_11542, plain, (~r2_relset_1('#skF_8', '#skF_8', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11508, c_11508, c_11264])).
% 9.08/3.31  tff(c_11693, plain, (~r2_relset_1('#skF_8', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11557, c_11542])).
% 9.08/3.31  tff(c_13495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13490, c_11693])).
% 9.08/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.08/3.31  
% 9.08/3.31  Inference rules
% 9.08/3.31  ----------------------
% 9.08/3.31  #Ref     : 0
% 9.08/3.31  #Sup     : 3040
% 9.08/3.31  #Fact    : 0
% 9.08/3.31  #Define  : 0
% 9.08/3.31  #Split   : 18
% 9.08/3.31  #Chain   : 0
% 9.08/3.31  #Close   : 0
% 9.08/3.31  
% 9.08/3.31  Ordering : KBO
% 9.08/3.31  
% 9.08/3.31  Simplification rules
% 9.08/3.31  ----------------------
% 9.08/3.31  #Subsume      : 940
% 9.08/3.31  #Demod        : 2033
% 9.08/3.31  #Tautology    : 924
% 9.08/3.31  #SimpNegUnit  : 115
% 9.08/3.31  #BackRed      : 136
% 9.08/3.31  
% 9.08/3.31  #Partial instantiations: 0
% 9.08/3.31  #Strategies tried      : 1
% 9.08/3.31  
% 9.08/3.31  Timing (in seconds)
% 9.08/3.31  ----------------------
% 9.08/3.31  Preprocessing        : 0.35
% 9.08/3.31  Parsing              : 0.18
% 9.08/3.31  CNF conversion       : 0.03
% 9.08/3.31  Main loop            : 2.18
% 9.08/3.31  Inferencing          : 0.63
% 9.08/3.31  Reduction            : 0.74
% 9.08/3.31  Demodulation         : 0.52
% 9.08/3.31  BG Simplification    : 0.07
% 9.08/3.31  Subsumption          : 0.58
% 9.08/3.31  Abstraction          : 0.08
% 9.08/3.31  MUC search           : 0.00
% 9.08/3.31  Cooper               : 0.00
% 9.08/3.31  Total                : 2.57
% 9.08/3.32  Index Insertion      : 0.00
% 9.08/3.32  Index Deletion       : 0.00
% 9.08/3.32  Index Matching       : 0.00
% 9.08/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
