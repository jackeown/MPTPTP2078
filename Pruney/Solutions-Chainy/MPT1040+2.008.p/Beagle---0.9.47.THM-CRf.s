%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:02 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 536 expanded)
%              Number of leaves         :   39 ( 186 expanded)
%              Depth                    :   12
%              Number of atoms          :  193 (1490 expanded)
%              Number of equality atoms :   34 ( 509 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_10 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_14,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ~ r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_92,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_82,plain,(
    r1_partfun1('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_90,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_88,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_104,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_104])).

tff(c_80,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_102,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_110,plain,(
    '#skF_3' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_102])).

tff(c_86,plain,(
    v1_funct_2('#skF_11','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_84,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_365,plain,(
    ! [C_110,A_111,B_112] :
      ( v1_partfun1(C_110,A_111)
      | ~ v1_funct_2(C_110,A_111,B_112)
      | ~ v1_funct_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | v1_xboole_0(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_375,plain,
    ( v1_partfun1('#skF_11','#skF_8')
    | ~ v1_funct_2('#skF_11','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_11')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_84,c_365])).

tff(c_390,plain,
    ( v1_partfun1('#skF_11','#skF_8')
    | v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_375])).

tff(c_395,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,(
    ! [A_10] :
      ( A_10 = '#skF_3'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_12])).

tff(c_400,plain,(
    '#skF_3' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_395,c_109])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_400])).

tff(c_406,plain,(
    v1_partfun1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_1757,plain,(
    ! [F_267,A_268,B_269,C_270] :
      ( r2_hidden(F_267,k5_partfun1(A_268,B_269,C_270))
      | ~ r1_partfun1(C_270,F_267)
      | ~ v1_partfun1(F_267,A_268)
      | ~ m1_subset_1(F_267,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269)))
      | ~ v1_funct_1(F_267)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269)))
      | ~ v1_funct_1(C_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1764,plain,(
    ! [C_270] :
      ( r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_9',C_270))
      | ~ r1_partfun1(C_270,'#skF_11')
      | ~ v1_partfun1('#skF_11','#skF_8')
      | ~ v1_funct_1('#skF_11')
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
      | ~ v1_funct_1(C_270) ) ),
    inference(resolution,[status(thm)],[c_84,c_1757])).

tff(c_2722,plain,(
    ! [C_323] :
      ( r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_9',C_323))
      | ~ r1_partfun1(C_323,'#skF_11')
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
      | ~ v1_funct_1(C_323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_406,c_1764])).

tff(c_2736,plain,
    ( r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_9','#skF_10'))
    | ~ r1_partfun1('#skF_10','#skF_11')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_90,c_2722])).

tff(c_2745,plain,(
    r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_2736])).

tff(c_2747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2745])).

tff(c_2748,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_2770,plain,(
    ! [A_326] :
      ( A_326 = '#skF_8'
      | ~ v1_xboole_0(A_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2748,c_12])).

tff(c_2774,plain,(
    '#skF_3' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_14,c_2770])).

tff(c_2775,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2774,c_14])).

tff(c_2853,plain,(
    ! [A_337,B_338] :
      ( r2_hidden('#skF_2'(A_337,B_338),A_337)
      | r1_tarski(A_337,B_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2857,plain,(
    ! [A_337,B_338] :
      ( ~ v1_xboole_0(A_337)
      | r1_tarski(A_337,B_338) ) ),
    inference(resolution,[status(thm)],[c_2853,c_2])).

tff(c_24,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2750,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2748,c_2748,c_24])).

tff(c_2749,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_2755,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2748,c_2749])).

tff(c_2801,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2750,c_2755,c_90])).

tff(c_2819,plain,(
    ! [A_332,B_333] :
      ( r1_tarski(A_332,B_333)
      | ~ m1_subset_1(A_332,k1_zfmisc_1(B_333)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2831,plain,(
    r1_tarski('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_2801,c_2819])).

tff(c_2871,plain,(
    ! [B_343,A_344] :
      ( B_343 = A_344
      | ~ r1_tarski(B_343,A_344)
      | ~ r1_tarski(A_344,B_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2887,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_2831,c_2871])).

tff(c_2893,plain,(
    ~ r1_tarski('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2887])).

tff(c_2896,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2857,c_2893])).

tff(c_2900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2775,c_2896])).

tff(c_2901,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2887])).

tff(c_2935,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2901,c_92])).

tff(c_2933,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2901,c_2801])).

tff(c_2804,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2750,c_2755,c_84])).

tff(c_2830,plain,(
    r1_tarski('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_2804,c_2819])).

tff(c_2888,plain,
    ( '#skF_11' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_11') ),
    inference(resolution,[status(thm)],[c_2830,c_2871])).

tff(c_2903,plain,(
    ~ r1_tarski('#skF_8','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_2888])).

tff(c_2917,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2857,c_2903])).

tff(c_2921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2775,c_2917])).

tff(c_2922,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2888])).

tff(c_2934,plain,(
    r1_partfun1('#skF_8','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2901,c_82])).

tff(c_2953,plain,(
    r1_partfun1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2922,c_2934])).

tff(c_26,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2785,plain,(
    ! [B_14] : k2_zfmisc_1('#skF_8',B_14) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2748,c_2748,c_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2810,plain,(
    ! [A_331] : m1_subset_1(k6_partfun1(A_331),k1_zfmisc_1(k2_zfmisc_1(A_331,A_331))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2814,plain,(
    m1_subset_1(k6_partfun1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2785,c_2810])).

tff(c_2959,plain,(
    ! [C_347,B_348,A_349] :
      ( ~ v1_xboole_0(C_347)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(C_347))
      | ~ r2_hidden(A_349,B_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2965,plain,(
    ! [A_349] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_349,k6_partfun1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2814,c_2959])).

tff(c_2994,plain,(
    ! [A_352] : ~ r2_hidden(A_352,k6_partfun1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2775,c_2965])).

tff(c_3004,plain,(
    v1_xboole_0(k6_partfun1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_4,c_2994])).

tff(c_2769,plain,(
    ! [A_10] :
      ( A_10 = '#skF_8'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2748,c_12])).

tff(c_3008,plain,(
    k6_partfun1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3004,c_2769])).

tff(c_74,plain,(
    ! [A_66] : v1_partfun1(k6_partfun1(A_66),A_66) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_76,plain,(
    ! [A_66] : m1_subset_1(k6_partfun1(A_66),k1_zfmisc_1(k2_zfmisc_1(A_66,A_66))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3889,plain,(
    ! [F_505,A_506,B_507,C_508] :
      ( r2_hidden(F_505,k5_partfun1(A_506,B_507,C_508))
      | ~ r1_partfun1(C_508,F_505)
      | ~ v1_partfun1(F_505,A_506)
      | ~ m1_subset_1(F_505,k1_zfmisc_1(k2_zfmisc_1(A_506,B_507)))
      | ~ v1_funct_1(F_505)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_506,B_507)))
      | ~ v1_funct_1(C_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3896,plain,(
    ! [A_66,C_508] :
      ( r2_hidden(k6_partfun1(A_66),k5_partfun1(A_66,A_66,C_508))
      | ~ r1_partfun1(C_508,k6_partfun1(A_66))
      | ~ v1_partfun1(k6_partfun1(A_66),A_66)
      | ~ v1_funct_1(k6_partfun1(A_66))
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_66,A_66)))
      | ~ v1_funct_1(C_508) ) ),
    inference(resolution,[status(thm)],[c_76,c_3889])).

tff(c_4131,plain,(
    ! [A_556,C_557] :
      ( r2_hidden(k6_partfun1(A_556),k5_partfun1(A_556,A_556,C_557))
      | ~ r1_partfun1(C_557,k6_partfun1(A_556))
      | ~ v1_funct_1(k6_partfun1(A_556))
      | ~ m1_subset_1(C_557,k1_zfmisc_1(k2_zfmisc_1(A_556,A_556)))
      | ~ v1_funct_1(C_557) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3896])).

tff(c_4143,plain,(
    ! [C_557] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8',C_557))
      | ~ r1_partfun1(C_557,k6_partfun1('#skF_8'))
      | ~ v1_funct_1(k6_partfun1('#skF_8'))
      | ~ m1_subset_1(C_557,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8')))
      | ~ v1_funct_1(C_557) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3008,c_4131])).

tff(c_4151,plain,(
    ! [C_562] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8',C_562))
      | ~ r1_partfun1(C_562,'#skF_8')
      | ~ m1_subset_1(C_562,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1(C_562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2785,c_2935,c_3008,c_3008,c_4143])).

tff(c_2803,plain,(
    ~ r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_8','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2755,c_78])).

tff(c_2932,plain,(
    ~ r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2901,c_2803])).

tff(c_2993,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2922,c_2932])).

tff(c_4160,plain,
    ( ~ r1_partfun1('#skF_8','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4151,c_2993])).

tff(c_4171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2935,c_2933,c_2953,c_4160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.14  
% 5.91/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.14  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_10 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2
% 5.91/2.14  
% 5.91/2.14  %Foreground sorts:
% 5.91/2.14  
% 5.91/2.14  
% 5.91/2.14  %Background operators:
% 5.91/2.14  
% 5.91/2.14  
% 5.91/2.14  %Foreground operators:
% 5.91/2.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.91/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.91/2.14  tff('#skF_11', type, '#skF_11': $i).
% 5.91/2.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.91/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.91/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.91/2.14  tff('#skF_10', type, '#skF_10': $i).
% 5.91/2.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.91/2.14  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i * $i) > $i).
% 5.91/2.14  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.91/2.14  tff('#skF_3', type, '#skF_3': $i).
% 5.91/2.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 5.91/2.14  tff('#skF_9', type, '#skF_9': $i).
% 5.91/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.91/2.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.91/2.14  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.91/2.14  tff('#skF_8', type, '#skF_8': $i).
% 5.91/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.14  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.91/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.91/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.91/2.14  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 5.91/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.91/2.14  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 5.91/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.91/2.14  
% 5.91/2.16  tff(f_44, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 5.91/2.16  tff(f_127, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 5.91/2.16  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.91/2.16  tff(f_81, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.91/2.16  tff(f_102, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 5.91/2.16  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.91/2.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.91/2.16  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.91/2.16  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.91/2.16  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.91/2.16  tff(f_106, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.91/2.16  tff(f_67, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.91/2.16  tff(c_14, plain, (v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.91/2.16  tff(c_78, plain, (~r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.91/2.16  tff(c_92, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.91/2.16  tff(c_82, plain, (r1_partfun1('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.91/2.16  tff(c_90, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.91/2.16  tff(c_88, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.91/2.16  tff(c_104, plain, (![A_71]: (k1_xboole_0=A_71 | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.91/2.16  tff(c_108, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14, c_104])).
% 5.91/2.16  tff(c_80, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.91/2.16  tff(c_102, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_80])).
% 5.91/2.16  tff(c_110, plain, ('#skF_3'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_102])).
% 5.91/2.16  tff(c_86, plain, (v1_funct_2('#skF_11', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.91/2.16  tff(c_84, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.91/2.16  tff(c_365, plain, (![C_110, A_111, B_112]: (v1_partfun1(C_110, A_111) | ~v1_funct_2(C_110, A_111, B_112) | ~v1_funct_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | v1_xboole_0(B_112))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.91/2.16  tff(c_375, plain, (v1_partfun1('#skF_11', '#skF_8') | ~v1_funct_2('#skF_11', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_11') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_84, c_365])).
% 5.91/2.16  tff(c_390, plain, (v1_partfun1('#skF_11', '#skF_8') | v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_375])).
% 5.91/2.16  tff(c_395, plain, (v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_390])).
% 5.91/2.16  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.91/2.16  tff(c_109, plain, (![A_10]: (A_10='#skF_3' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_12])).
% 5.91/2.16  tff(c_400, plain, ('#skF_3'='#skF_9'), inference(resolution, [status(thm)], [c_395, c_109])).
% 5.91/2.16  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_400])).
% 5.91/2.16  tff(c_406, plain, (v1_partfun1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_390])).
% 5.91/2.16  tff(c_1757, plain, (![F_267, A_268, B_269, C_270]: (r2_hidden(F_267, k5_partfun1(A_268, B_269, C_270)) | ~r1_partfun1(C_270, F_267) | ~v1_partfun1(F_267, A_268) | ~m1_subset_1(F_267, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))) | ~v1_funct_1(F_267) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))) | ~v1_funct_1(C_270))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.91/2.16  tff(c_1764, plain, (![C_270]: (r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_9', C_270)) | ~r1_partfun1(C_270, '#skF_11') | ~v1_partfun1('#skF_11', '#skF_8') | ~v1_funct_1('#skF_11') | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_1(C_270))), inference(resolution, [status(thm)], [c_84, c_1757])).
% 5.91/2.16  tff(c_2722, plain, (![C_323]: (r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_9', C_323)) | ~r1_partfun1(C_323, '#skF_11') | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_1(C_323))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_406, c_1764])).
% 5.91/2.16  tff(c_2736, plain, (r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_9', '#skF_10')) | ~r1_partfun1('#skF_10', '#skF_11') | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_90, c_2722])).
% 5.91/2.16  tff(c_2745, plain, (r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_82, c_2736])).
% 5.91/2.16  tff(c_2747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_2745])).
% 5.91/2.16  tff(c_2748, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 5.91/2.16  tff(c_2770, plain, (![A_326]: (A_326='#skF_8' | ~v1_xboole_0(A_326))), inference(demodulation, [status(thm), theory('equality')], [c_2748, c_12])).
% 5.91/2.16  tff(c_2774, plain, ('#skF_3'='#skF_8'), inference(resolution, [status(thm)], [c_14, c_2770])).
% 5.91/2.16  tff(c_2775, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2774, c_14])).
% 5.91/2.16  tff(c_2853, plain, (![A_337, B_338]: (r2_hidden('#skF_2'(A_337, B_338), A_337) | r1_tarski(A_337, B_338))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.91/2.16  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.91/2.16  tff(c_2857, plain, (![A_337, B_338]: (~v1_xboole_0(A_337) | r1_tarski(A_337, B_338))), inference(resolution, [status(thm)], [c_2853, c_2])).
% 5.91/2.16  tff(c_24, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.91/2.16  tff(c_2750, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2748, c_2748, c_24])).
% 5.91/2.16  tff(c_2749, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_80])).
% 5.91/2.16  tff(c_2755, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2748, c_2749])).
% 5.91/2.16  tff(c_2801, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2750, c_2755, c_90])).
% 5.91/2.16  tff(c_2819, plain, (![A_332, B_333]: (r1_tarski(A_332, B_333) | ~m1_subset_1(A_332, k1_zfmisc_1(B_333)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.91/2.16  tff(c_2831, plain, (r1_tarski('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_2801, c_2819])).
% 5.91/2.16  tff(c_2871, plain, (![B_343, A_344]: (B_343=A_344 | ~r1_tarski(B_343, A_344) | ~r1_tarski(A_344, B_343))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.91/2.16  tff(c_2887, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_2831, c_2871])).
% 5.91/2.16  tff(c_2893, plain, (~r1_tarski('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_2887])).
% 5.91/2.16  tff(c_2896, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_2857, c_2893])).
% 5.91/2.16  tff(c_2900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2775, c_2896])).
% 5.91/2.16  tff(c_2901, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_2887])).
% 5.91/2.16  tff(c_2935, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2901, c_92])).
% 5.91/2.16  tff(c_2933, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2901, c_2801])).
% 5.91/2.16  tff(c_2804, plain, (m1_subset_1('#skF_11', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2750, c_2755, c_84])).
% 5.91/2.16  tff(c_2830, plain, (r1_tarski('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_2804, c_2819])).
% 5.91/2.16  tff(c_2888, plain, ('#skF_11'='#skF_8' | ~r1_tarski('#skF_8', '#skF_11')), inference(resolution, [status(thm)], [c_2830, c_2871])).
% 5.91/2.16  tff(c_2903, plain, (~r1_tarski('#skF_8', '#skF_11')), inference(splitLeft, [status(thm)], [c_2888])).
% 5.91/2.16  tff(c_2917, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_2857, c_2903])).
% 5.91/2.16  tff(c_2921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2775, c_2917])).
% 5.91/2.16  tff(c_2922, plain, ('#skF_11'='#skF_8'), inference(splitRight, [status(thm)], [c_2888])).
% 5.91/2.16  tff(c_2934, plain, (r1_partfun1('#skF_8', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_2901, c_82])).
% 5.91/2.16  tff(c_2953, plain, (r1_partfun1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2922, c_2934])).
% 5.91/2.16  tff(c_26, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.91/2.16  tff(c_2785, plain, (![B_14]: (k2_zfmisc_1('#skF_8', B_14)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2748, c_2748, c_26])).
% 5.91/2.16  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.91/2.16  tff(c_2810, plain, (![A_331]: (m1_subset_1(k6_partfun1(A_331), k1_zfmisc_1(k2_zfmisc_1(A_331, A_331))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.91/2.16  tff(c_2814, plain, (m1_subset_1(k6_partfun1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2785, c_2810])).
% 5.91/2.16  tff(c_2959, plain, (![C_347, B_348, A_349]: (~v1_xboole_0(C_347) | ~m1_subset_1(B_348, k1_zfmisc_1(C_347)) | ~r2_hidden(A_349, B_348))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.91/2.16  tff(c_2965, plain, (![A_349]: (~v1_xboole_0('#skF_8') | ~r2_hidden(A_349, k6_partfun1('#skF_8')))), inference(resolution, [status(thm)], [c_2814, c_2959])).
% 5.91/2.16  tff(c_2994, plain, (![A_352]: (~r2_hidden(A_352, k6_partfun1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_2775, c_2965])).
% 5.91/2.16  tff(c_3004, plain, (v1_xboole_0(k6_partfun1('#skF_8'))), inference(resolution, [status(thm)], [c_4, c_2994])).
% 5.91/2.16  tff(c_2769, plain, (![A_10]: (A_10='#skF_8' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_2748, c_12])).
% 5.91/2.16  tff(c_3008, plain, (k6_partfun1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_3004, c_2769])).
% 5.91/2.16  tff(c_74, plain, (![A_66]: (v1_partfun1(k6_partfun1(A_66), A_66))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.91/2.16  tff(c_76, plain, (![A_66]: (m1_subset_1(k6_partfun1(A_66), k1_zfmisc_1(k2_zfmisc_1(A_66, A_66))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.91/2.16  tff(c_3889, plain, (![F_505, A_506, B_507, C_508]: (r2_hidden(F_505, k5_partfun1(A_506, B_507, C_508)) | ~r1_partfun1(C_508, F_505) | ~v1_partfun1(F_505, A_506) | ~m1_subset_1(F_505, k1_zfmisc_1(k2_zfmisc_1(A_506, B_507))) | ~v1_funct_1(F_505) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_506, B_507))) | ~v1_funct_1(C_508))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.91/2.16  tff(c_3896, plain, (![A_66, C_508]: (r2_hidden(k6_partfun1(A_66), k5_partfun1(A_66, A_66, C_508)) | ~r1_partfun1(C_508, k6_partfun1(A_66)) | ~v1_partfun1(k6_partfun1(A_66), A_66) | ~v1_funct_1(k6_partfun1(A_66)) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_66, A_66))) | ~v1_funct_1(C_508))), inference(resolution, [status(thm)], [c_76, c_3889])).
% 5.91/2.16  tff(c_4131, plain, (![A_556, C_557]: (r2_hidden(k6_partfun1(A_556), k5_partfun1(A_556, A_556, C_557)) | ~r1_partfun1(C_557, k6_partfun1(A_556)) | ~v1_funct_1(k6_partfun1(A_556)) | ~m1_subset_1(C_557, k1_zfmisc_1(k2_zfmisc_1(A_556, A_556))) | ~v1_funct_1(C_557))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3896])).
% 5.91/2.16  tff(c_4143, plain, (![C_557]: (r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', C_557)) | ~r1_partfun1(C_557, k6_partfun1('#skF_8')) | ~v1_funct_1(k6_partfun1('#skF_8')) | ~m1_subset_1(C_557, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8'))) | ~v1_funct_1(C_557))), inference(superposition, [status(thm), theory('equality')], [c_3008, c_4131])).
% 5.91/2.16  tff(c_4151, plain, (![C_562]: (r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', C_562)) | ~r1_partfun1(C_562, '#skF_8') | ~m1_subset_1(C_562, k1_zfmisc_1('#skF_8')) | ~v1_funct_1(C_562))), inference(demodulation, [status(thm), theory('equality')], [c_2785, c_2935, c_3008, c_3008, c_4143])).
% 5.91/2.16  tff(c_2803, plain, (~r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_8', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_2755, c_78])).
% 5.91/2.16  tff(c_2932, plain, (~r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2901, c_2803])).
% 5.91/2.16  tff(c_2993, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2922, c_2932])).
% 5.91/2.16  tff(c_4160, plain, (~r1_partfun1('#skF_8', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_4151, c_2993])).
% 5.91/2.16  tff(c_4171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2935, c_2933, c_2953, c_4160])).
% 5.91/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.16  
% 5.91/2.16  Inference rules
% 5.91/2.16  ----------------------
% 5.91/2.16  #Ref     : 0
% 5.91/2.16  #Sup     : 940
% 5.91/2.16  #Fact    : 0
% 5.91/2.16  #Define  : 0
% 5.91/2.16  #Split   : 15
% 5.91/2.16  #Chain   : 0
% 5.91/2.16  #Close   : 0
% 5.91/2.16  
% 5.91/2.16  Ordering : KBO
% 5.91/2.16  
% 5.91/2.16  Simplification rules
% 5.91/2.16  ----------------------
% 5.91/2.16  #Subsume      : 372
% 5.91/2.16  #Demod        : 690
% 5.91/2.16  #Tautology    : 209
% 5.91/2.16  #SimpNegUnit  : 26
% 5.91/2.16  #BackRed      : 97
% 5.91/2.16  
% 5.91/2.16  #Partial instantiations: 0
% 5.91/2.16  #Strategies tried      : 1
% 5.91/2.16  
% 5.91/2.16  Timing (in seconds)
% 5.91/2.16  ----------------------
% 5.91/2.16  Preprocessing        : 0.35
% 5.91/2.16  Parsing              : 0.16
% 5.91/2.16  CNF conversion       : 0.03
% 5.91/2.16  Main loop            : 1.01
% 5.91/2.16  Inferencing          : 0.32
% 5.91/2.16  Reduction            : 0.33
% 5.91/2.16  Demodulation         : 0.23
% 5.91/2.16  BG Simplification    : 0.04
% 5.91/2.16  Subsumption          : 0.24
% 5.91/2.16  Abstraction          : 0.05
% 5.91/2.16  MUC search           : 0.00
% 5.91/2.16  Cooper               : 0.00
% 5.91/2.16  Total                : 1.40
% 5.91/2.16  Index Insertion      : 0.00
% 5.91/2.16  Index Deletion       : 0.00
% 5.91/2.16  Index Matching       : 0.00
% 5.91/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
