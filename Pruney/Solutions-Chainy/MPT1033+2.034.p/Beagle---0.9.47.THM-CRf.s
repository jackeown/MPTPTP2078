%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:55 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 283 expanded)
%              Number of leaves         :   32 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  166 ( 960 expanded)
%              Number of equality atoms :   31 ( 254 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_112,axiom,(
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

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_521,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( r2_relset_1(A_104,B_105,C_106,C_106)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_613,plain,(
    ! [C_108] :
      ( r2_relset_1('#skF_3','#skF_4',C_108,C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_46,c_521])).

tff(c_641,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_613])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_396,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_partfun1(C_97,A_98)
      | ~ v1_funct_2(C_97,A_98,B_99)
      | ~ v1_funct_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | v1_xboole_0(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_411,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_396])).

tff(c_434,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_411])).

tff(c_440,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_434])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_2'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_158,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_233,plain,(
    ! [B_64,A_65,A_66] :
      ( ~ v1_xboole_0(B_64)
      | ~ r2_hidden(A_65,A_66)
      | ~ r1_tarski(A_66,B_64) ) ),
    inference(resolution,[status(thm)],[c_20,c_158])).

tff(c_241,plain,(
    ! [B_70,A_71] :
      ( ~ v1_xboole_0(B_70)
      | ~ r1_tarski(A_71,B_70)
      | k1_xboole_0 = A_71 ) ),
    inference(resolution,[status(thm)],[c_28,c_233])).

tff(c_262,plain,(
    ! [B_2] :
      ( ~ v1_xboole_0(B_2)
      | k1_xboole_0 = B_2 ) ),
    inference(resolution,[status(thm)],[c_6,c_241])).

tff(c_443,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_440,c_262])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_443])).

tff(c_448,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_449,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_414,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_396])).

tff(c_437,plain,
    ( v1_partfun1('#skF_6','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_414])).

tff(c_450,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_437])).

tff(c_44,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_646,plain,(
    ! [D_109,C_110,A_111,B_112] :
      ( D_109 = C_110
      | ~ r1_partfun1(C_110,D_109)
      | ~ v1_partfun1(D_109,A_111)
      | ~ v1_partfun1(C_110,A_111)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_1(D_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_648,plain,(
    ! [A_111,B_112] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_111)
      | ~ v1_partfun1('#skF_5',A_111)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_646])).

tff(c_651,plain,(
    ! [A_111,B_112] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_111)
      | ~ v1_partfun1('#skF_5',A_111)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_648])).

tff(c_1414,plain,(
    ! [A_182,B_183] :
      ( ~ v1_partfun1('#skF_6',A_182)
      | ~ v1_partfun1('#skF_5',A_182)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(splitLeft,[status(thm)],[c_651])).

tff(c_1420,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_52,c_1414])).

tff(c_1431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_448,c_450,c_1420])).

tff(c_1432,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_651])).

tff(c_40,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1439,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_40])).

tff(c_1449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_1439])).

tff(c_1451,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1450,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1459,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1450])).

tff(c_16,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1452,plain,(
    ! [A_7] : m1_subset_1('#skF_3',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_16])).

tff(c_1479,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_1452])).

tff(c_1863,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( r2_relset_1(A_241,B_242,C_243,C_243)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242)))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2037,plain,(
    ! [A_255,B_256,C_257] :
      ( r2_relset_1(A_255,B_256,C_257,C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(resolution,[status(thm)],[c_1479,c_1863])).

tff(c_2065,plain,(
    ! [A_255,B_256] : r2_relset_1(A_255,B_256,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1479,c_2037])).

tff(c_1503,plain,(
    ! [A_191,B_192] :
      ( r1_tarski(A_191,B_192)
      | ~ m1_subset_1(A_191,k1_zfmisc_1(B_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1523,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(resolution,[status(thm)],[c_1479,c_1503])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1454,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_1450,c_10])).

tff(c_1471,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_1459,c_1454])).

tff(c_1499,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1471,c_1459,c_52])).

tff(c_1521,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1499,c_1503])).

tff(c_1539,plain,(
    ! [B_197,A_198] :
      ( B_197 = A_198
      | ~ r1_tarski(B_197,A_198)
      | ~ r1_tarski(A_198,B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1547,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1521,c_1539])).

tff(c_1557,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1547])).

tff(c_1498,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1471,c_1459,c_46])).

tff(c_1522,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1498,c_1503])).

tff(c_1545,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_1522,c_1539])).

tff(c_1554,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1545])).

tff(c_1497,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_40])).

tff(c_1565,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1554,c_1497])).

tff(c_1606,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_1565])).

tff(c_2092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2065,c_1606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:14:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.69  
% 4.14/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.70  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.14/1.70  
% 4.14/1.70  %Foreground sorts:
% 4.14/1.70  
% 4.14/1.70  
% 4.14/1.70  %Background operators:
% 4.14/1.70  
% 4.14/1.70  
% 4.14/1.70  %Foreground operators:
% 4.14/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.14/1.70  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.14/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.14/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.14/1.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.14/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.14/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.14/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.14/1.70  tff('#skF_6', type, '#skF_6': $i).
% 4.14/1.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.14/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.14/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.14/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.14/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.14/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.14/1.70  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 4.14/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.14/1.70  
% 4.14/1.71  tff(f_135, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 4.14/1.71  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 4.14/1.71  tff(f_95, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.14/1.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.14/1.71  tff(f_81, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 4.14/1.71  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.14/1.71  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.14/1.71  tff(f_112, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 4.14/1.71  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.14/1.71  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.14/1.71  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.14/1.71  tff(c_521, plain, (![A_104, B_105, C_106, D_107]: (r2_relset_1(A_104, B_105, C_106, C_106) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.14/1.71  tff(c_613, plain, (![C_108]: (r2_relset_1('#skF_3', '#skF_4', C_108, C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_46, c_521])).
% 4.14/1.71  tff(c_641, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_613])).
% 4.14/1.71  tff(c_42, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.14/1.71  tff(c_82, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_42])).
% 4.14/1.71  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.14/1.71  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.14/1.71  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.14/1.71  tff(c_396, plain, (![C_97, A_98, B_99]: (v1_partfun1(C_97, A_98) | ~v1_funct_2(C_97, A_98, B_99) | ~v1_funct_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | v1_xboole_0(B_99))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.14/1.71  tff(c_411, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_396])).
% 4.14/1.71  tff(c_434, plain, (v1_partfun1('#skF_5', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_411])).
% 4.14/1.71  tff(c_440, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_434])).
% 4.14/1.71  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/1.71  tff(c_28, plain, (![A_20]: (r2_hidden('#skF_2'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.14/1.71  tff(c_20, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.14/1.71  tff(c_158, plain, (![C_57, B_58, A_59]: (~v1_xboole_0(C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.14/1.71  tff(c_233, plain, (![B_64, A_65, A_66]: (~v1_xboole_0(B_64) | ~r2_hidden(A_65, A_66) | ~r1_tarski(A_66, B_64))), inference(resolution, [status(thm)], [c_20, c_158])).
% 4.14/1.71  tff(c_241, plain, (![B_70, A_71]: (~v1_xboole_0(B_70) | ~r1_tarski(A_71, B_70) | k1_xboole_0=A_71)), inference(resolution, [status(thm)], [c_28, c_233])).
% 4.14/1.71  tff(c_262, plain, (![B_2]: (~v1_xboole_0(B_2) | k1_xboole_0=B_2)), inference(resolution, [status(thm)], [c_6, c_241])).
% 4.14/1.71  tff(c_443, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_440, c_262])).
% 4.14/1.71  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_443])).
% 4.14/1.71  tff(c_448, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_434])).
% 4.14/1.71  tff(c_449, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_434])).
% 4.14/1.71  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.14/1.71  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.14/1.71  tff(c_414, plain, (v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_396])).
% 4.14/1.71  tff(c_437, plain, (v1_partfun1('#skF_6', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_414])).
% 4.14/1.71  tff(c_450, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_449, c_437])).
% 4.14/1.71  tff(c_44, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.14/1.71  tff(c_646, plain, (![D_109, C_110, A_111, B_112]: (D_109=C_110 | ~r1_partfun1(C_110, D_109) | ~v1_partfun1(D_109, A_111) | ~v1_partfun1(C_110, A_111) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_1(D_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.14/1.71  tff(c_648, plain, (![A_111, B_112]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_111) | ~v1_partfun1('#skF_5', A_111) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_646])).
% 4.14/1.71  tff(c_651, plain, (![A_111, B_112]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_111) | ~v1_partfun1('#skF_5', A_111) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_648])).
% 4.14/1.71  tff(c_1414, plain, (![A_182, B_183]: (~v1_partfun1('#skF_6', A_182) | ~v1_partfun1('#skF_5', A_182) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(splitLeft, [status(thm)], [c_651])).
% 4.14/1.71  tff(c_1420, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_52, c_1414])).
% 4.14/1.71  tff(c_1431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_448, c_450, c_1420])).
% 4.14/1.71  tff(c_1432, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_651])).
% 4.14/1.71  tff(c_40, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.14/1.71  tff(c_1439, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_40])).
% 4.14/1.71  tff(c_1449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_641, c_1439])).
% 4.14/1.71  tff(c_1451, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 4.14/1.71  tff(c_1450, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 4.14/1.71  tff(c_1459, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1450])).
% 4.14/1.71  tff(c_16, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.14/1.71  tff(c_1452, plain, (![A_7]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_16])).
% 4.14/1.71  tff(c_1479, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_1459, c_1452])).
% 4.14/1.71  tff(c_1863, plain, (![A_241, B_242, C_243, D_244]: (r2_relset_1(A_241, B_242, C_243, C_243) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.14/1.71  tff(c_2037, plain, (![A_255, B_256, C_257]: (r2_relset_1(A_255, B_256, C_257, C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(resolution, [status(thm)], [c_1479, c_1863])).
% 4.14/1.71  tff(c_2065, plain, (![A_255, B_256]: (r2_relset_1(A_255, B_256, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_1479, c_2037])).
% 4.14/1.71  tff(c_1503, plain, (![A_191, B_192]: (r1_tarski(A_191, B_192) | ~m1_subset_1(A_191, k1_zfmisc_1(B_192)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.14/1.71  tff(c_1523, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(resolution, [status(thm)], [c_1479, c_1503])).
% 4.14/1.71  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.14/1.71  tff(c_1454, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1450, c_1450, c_10])).
% 4.14/1.71  tff(c_1471, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1459, c_1459, c_1454])).
% 4.14/1.71  tff(c_1499, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1471, c_1459, c_52])).
% 4.14/1.71  tff(c_1521, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1499, c_1503])).
% 4.14/1.71  tff(c_1539, plain, (![B_197, A_198]: (B_197=A_198 | ~r1_tarski(B_197, A_198) | ~r1_tarski(A_198, B_197))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/1.71  tff(c_1547, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1521, c_1539])).
% 4.14/1.71  tff(c_1557, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1547])).
% 4.14/1.71  tff(c_1498, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1471, c_1459, c_46])).
% 4.14/1.71  tff(c_1522, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1498, c_1503])).
% 4.14/1.71  tff(c_1545, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_1522, c_1539])).
% 4.14/1.71  tff(c_1554, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1545])).
% 4.14/1.71  tff(c_1497, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1459, c_40])).
% 4.14/1.71  tff(c_1565, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1554, c_1497])).
% 4.14/1.71  tff(c_1606, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1557, c_1565])).
% 4.14/1.71  tff(c_2092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2065, c_1606])).
% 4.14/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.71  
% 4.14/1.71  Inference rules
% 4.14/1.71  ----------------------
% 4.14/1.71  #Ref     : 0
% 4.14/1.71  #Sup     : 469
% 4.14/1.71  #Fact    : 0
% 4.14/1.71  #Define  : 0
% 4.14/1.71  #Split   : 16
% 4.14/1.71  #Chain   : 0
% 4.14/1.71  #Close   : 0
% 4.14/1.71  
% 4.14/1.71  Ordering : KBO
% 4.14/1.71  
% 4.14/1.71  Simplification rules
% 4.14/1.71  ----------------------
% 4.14/1.71  #Subsume      : 116
% 4.14/1.71  #Demod        : 307
% 4.14/1.71  #Tautology    : 167
% 4.14/1.71  #SimpNegUnit  : 4
% 4.14/1.71  #BackRed      : 31
% 4.14/1.71  
% 4.14/1.71  #Partial instantiations: 0
% 4.14/1.71  #Strategies tried      : 1
% 4.14/1.71  
% 4.14/1.71  Timing (in seconds)
% 4.14/1.71  ----------------------
% 4.14/1.72  Preprocessing        : 0.31
% 4.14/1.72  Parsing              : 0.17
% 4.14/1.72  CNF conversion       : 0.02
% 4.14/1.72  Main loop            : 0.59
% 4.14/1.72  Inferencing          : 0.20
% 4.14/1.72  Reduction            : 0.19
% 4.14/1.72  Demodulation         : 0.13
% 4.14/1.72  BG Simplification    : 0.02
% 4.14/1.72  Subsumption          : 0.12
% 4.14/1.72  Abstraction          : 0.03
% 4.14/1.72  MUC search           : 0.00
% 4.14/1.72  Cooper               : 0.00
% 4.14/1.72  Total                : 0.94
% 4.14/1.72  Index Insertion      : 0.00
% 4.14/1.72  Index Deletion       : 0.00
% 4.14/1.72  Index Matching       : 0.00
% 4.14/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
