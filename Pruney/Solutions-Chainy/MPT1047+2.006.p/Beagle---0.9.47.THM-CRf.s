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
% DateTime   : Thu Dec  3 10:17:07 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :  214 (5154 expanded)
%              Number of leaves         :   31 (1759 expanded)
%              Depth                    :   30
%              Number of atoms          :  684 (21096 expanded)
%              Number of equality atoms :  223 (4771 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,k1_tarski(B))
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
           => k5_partfun1(A,k1_tarski(B),C) = k1_tarski(D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C] :
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

tff(f_51,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
         => r1_partfun1(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

tff(f_96,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( r2_hidden(D,k5_partfun1(A,B,C))
         => ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_179,plain,(
    ! [B_69,C_70,A_71] :
      ( k1_xboole_0 = B_69
      | v1_partfun1(C_70,A_71)
      | ~ v1_funct_2(C_70,A_71,B_69)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_69)))
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_185,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_6','#skF_3')
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_179])).

tff(c_197,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_185])).

tff(c_199,plain,(
    v1_partfun1('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_2189,plain,(
    ! [B_363,D_364,A_365,C_366] :
      ( k1_xboole_0 = B_363
      | r2_hidden(D_364,k5_partfun1(A_365,B_363,C_366))
      | ~ r1_partfun1(C_366,D_364)
      | ~ m1_subset_1(D_364,k1_zfmisc_1(k2_zfmisc_1(A_365,B_363)))
      | ~ v1_funct_2(D_364,A_365,B_363)
      | ~ v1_funct_1(D_364)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_365,B_363)))
      | ~ v1_funct_1(C_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2193,plain,(
    ! [C_366] :
      ( k1_tarski('#skF_4') = k1_xboole_0
      | r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_366))
      | ~ r1_partfun1(C_366,'#skF_6')
      | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_366) ) ),
    inference(resolution,[status(thm)],[c_48,c_2189])).

tff(c_2203,plain,(
    ! [C_366] :
      ( k1_tarski('#skF_4') = k1_xboole_0
      | r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_366))
      | ~ r1_partfun1(C_366,'#skF_6')
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2193])).

tff(c_2222,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2203])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k2_zfmisc_1(A_11,k1_tarski(B_12)) != k1_xboole_0
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2247,plain,(
    ! [A_11] :
      ( k2_zfmisc_1(A_11,k1_xboole_0) != k1_xboole_0
      | k1_xboole_0 = A_11 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2222,c_24])).

tff(c_2274,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2247])).

tff(c_2263,plain,(
    ! [A_11] : k1_xboole_0 = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2247])).

tff(c_2621,plain,(
    ! [A_2136] : A_2136 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2274,c_2263])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_219,plain,(
    ! [C_80,D_81,A_82,B_83] :
      ( r1_partfun1(C_80,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_82,k1_tarski(B_83))))
      | ~ v1_funct_1(D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,k1_tarski(B_83))))
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_223,plain,(
    ! [C_80] :
      ( r1_partfun1(C_80,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_48,c_219])).

tff(c_247,plain,(
    ! [C_85] :
      ( r1_partfun1(C_85,'#skF_6')
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_223])).

tff(c_250,plain,
    ( r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_247])).

tff(c_256,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_250])).

tff(c_279,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r1_partfun1(C_92,D_91)
      | ~ v1_partfun1(D_91,A_93)
      | ~ v1_partfun1(C_92,A_93)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_1(D_91)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_283,plain,(
    ! [A_93,B_94] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_93)
      | ~ v1_partfun1('#skF_5',A_93)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_256,c_279])).

tff(c_294,plain,(
    ! [A_93,B_94] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_93)
      | ~ v1_partfun1('#skF_5',A_93)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_283])).

tff(c_303,plain,(
    ! [A_95,B_96] :
      ( ~ v1_partfun1('#skF_6',A_95)
      | ~ v1_partfun1('#skF_5',A_95)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_306,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_54,c_303])).

tff(c_315,plain,(
    ~ v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_199,c_306])).

tff(c_2667,plain,(
    ~ v1_partfun1('#skF_6','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2621,c_315])).

tff(c_2775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_2667])).

tff(c_2777,plain,(
    k1_tarski('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2203])).

tff(c_46,plain,(
    k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2778,plain,(
    ! [C_2777] :
      ( r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2777))
      | ~ r1_partfun1(C_2777,'#skF_6')
      | ~ m1_subset_1(C_2777,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_2777) ) ),
    inference(splitRight,[status(thm)],[c_2203])).

tff(c_2781,plain,
    ( r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5'))
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_2778])).

tff(c_2787,plain,(
    r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_256,c_2781])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [D_59,A_60,B_61,C_62] :
      ( v1_funct_1(D_59)
      | ~ r2_hidden(D_59,k5_partfun1(A_60,B_61,C_62))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2821,plain,(
    ! [A_2778,A_2779,B_2780,C_2781] :
      ( v1_funct_1('#skF_2'(A_2778,k5_partfun1(A_2779,B_2780,C_2781)))
      | ~ m1_subset_1(C_2781,k1_zfmisc_1(k2_zfmisc_1(A_2779,B_2780)))
      | ~ v1_funct_1(C_2781)
      | '#skF_1'(A_2778,k5_partfun1(A_2779,B_2780,C_2781)) = A_2778
      | k5_partfun1(A_2779,B_2780,C_2781) = k1_tarski(A_2778) ) ),
    inference(resolution,[status(thm)],[c_12,c_145])).

tff(c_2823,plain,(
    ! [A_2778] :
      ( v1_funct_1('#skF_2'(A_2778,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')))
      | ~ v1_funct_1('#skF_5')
      | '#skF_1'(A_2778,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = A_2778
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski(A_2778) ) ),
    inference(resolution,[status(thm)],[c_54,c_2821])).

tff(c_2832,plain,(
    ! [A_2778] :
      ( v1_funct_1('#skF_2'(A_2778,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')))
      | '#skF_1'(A_2778,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = A_2778
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski(A_2778) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2823])).

tff(c_200,plain,(
    ! [D_72,A_73,B_74,C_75] :
      ( v1_funct_2(D_72,A_73,B_74)
      | ~ r2_hidden(D_72,k5_partfun1(A_73,B_74,C_75))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_208,plain,(
    ! [A_1,A_73,B_74,C_75] :
      ( v1_funct_2('#skF_2'(A_1,k5_partfun1(A_73,B_74,C_75)),A_73,B_74)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_1(C_75)
      | '#skF_1'(A_1,k5_partfun1(A_73,B_74,C_75)) = A_1
      | k5_partfun1(A_73,B_74,C_75) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_200])).

tff(c_210,plain,(
    ! [D_76,A_77,B_78,C_79] :
      ( m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ r2_hidden(D_76,k5_partfun1(A_77,B_78,C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2853,plain,(
    ! [A_2798,A_2799,B_2800,C_2801] :
      ( m1_subset_1('#skF_2'(A_2798,k5_partfun1(A_2799,B_2800,C_2801)),k1_zfmisc_1(k2_zfmisc_1(A_2799,B_2800)))
      | ~ m1_subset_1(C_2801,k1_zfmisc_1(k2_zfmisc_1(A_2799,B_2800)))
      | ~ v1_funct_1(C_2801)
      | '#skF_1'(A_2798,k5_partfun1(A_2799,B_2800,C_2801)) = A_2798
      | k5_partfun1(A_2799,B_2800,C_2801) = k1_tarski(A_2798) ) ),
    inference(resolution,[status(thm)],[c_12,c_210])).

tff(c_30,plain,(
    ! [B_14,C_15,A_13] :
      ( k1_xboole_0 = B_14
      | v1_partfun1(C_15,A_13)
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2983,plain,(
    ! [B_2846,A_2847,A_2848,C_2849] :
      ( k1_xboole_0 = B_2846
      | v1_partfun1('#skF_2'(A_2847,k5_partfun1(A_2848,B_2846,C_2849)),A_2848)
      | ~ v1_funct_2('#skF_2'(A_2847,k5_partfun1(A_2848,B_2846,C_2849)),A_2848,B_2846)
      | ~ v1_funct_1('#skF_2'(A_2847,k5_partfun1(A_2848,B_2846,C_2849)))
      | ~ m1_subset_1(C_2849,k1_zfmisc_1(k2_zfmisc_1(A_2848,B_2846)))
      | ~ v1_funct_1(C_2849)
      | '#skF_1'(A_2847,k5_partfun1(A_2848,B_2846,C_2849)) = A_2847
      | k5_partfun1(A_2848,B_2846,C_2849) = k1_tarski(A_2847) ) ),
    inference(resolution,[status(thm)],[c_2853,c_30])).

tff(c_2987,plain,(
    ! [B_74,A_1,A_73,C_75] :
      ( k1_xboole_0 = B_74
      | v1_partfun1('#skF_2'(A_1,k5_partfun1(A_73,B_74,C_75)),A_73)
      | ~ v1_funct_1('#skF_2'(A_1,k5_partfun1(A_73,B_74,C_75)))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_1(C_75)
      | '#skF_1'(A_1,k5_partfun1(A_73,B_74,C_75)) = A_1
      | k5_partfun1(A_73,B_74,C_75) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_208,c_2983])).

tff(c_218,plain,(
    ! [A_1,A_77,B_78,C_79] :
      ( m1_subset_1('#skF_2'(A_1,k5_partfun1(A_77,B_78,C_79)),k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(C_79)
      | '#skF_1'(A_1,k5_partfun1(A_77,B_78,C_79)) = A_1
      | k5_partfun1(A_77,B_78,C_79) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_210])).

tff(c_232,plain,(
    ! [C_80] :
      ( r1_partfun1(C_80,'#skF_6')
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_223])).

tff(c_2891,plain,(
    ! [A_2802,C_2803] :
      ( r1_partfun1('#skF_2'(A_2802,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2803)),'#skF_6')
      | ~ v1_funct_1('#skF_2'(A_2802,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2803)))
      | ~ m1_subset_1(C_2803,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_2803)
      | '#skF_1'(A_2802,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2803)) = A_2802
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2803) = k1_tarski(A_2802) ) ),
    inference(resolution,[status(thm)],[c_2853,c_232])).

tff(c_34,plain,(
    ! [D_25,C_23,A_21,B_22] :
      ( D_25 = C_23
      | ~ r1_partfun1(C_23,D_25)
      | ~ v1_partfun1(D_25,A_21)
      | ~ v1_partfun1(C_23,A_21)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1(D_25)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2893,plain,(
    ! [A_2802,C_2803,A_21,B_22] :
      ( '#skF_2'(A_2802,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2803)) = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_21)
      | ~ v1_partfun1('#skF_2'(A_2802,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2803)),A_21)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_2'(A_2802,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2803)),k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1('#skF_2'(A_2802,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2803)))
      | ~ m1_subset_1(C_2803,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_2803)
      | '#skF_1'(A_2802,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2803)) = A_2802
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2803) = k1_tarski(A_2802) ) ),
    inference(resolution,[status(thm)],[c_2891,c_34])).

tff(c_3072,plain,(
    ! [A_2894,C_2895,A_2896,B_2897] :
      ( '#skF_2'(A_2894,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2895)) = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_2896)
      | ~ v1_partfun1('#skF_2'(A_2894,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2895)),A_2896)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_2896,B_2897)))
      | ~ m1_subset_1('#skF_2'(A_2894,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2895)),k1_zfmisc_1(k2_zfmisc_1(A_2896,B_2897)))
      | ~ v1_funct_1('#skF_2'(A_2894,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2895)))
      | ~ m1_subset_1(C_2895,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_2895)
      | '#skF_1'(A_2894,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2895)) = A_2894
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2895) = k1_tarski(A_2894) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2893])).

tff(c_3076,plain,(
    ! [A_1,C_79] :
      ( '#skF_2'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_79)) = '#skF_6'
      | ~ v1_partfun1('#skF_6','#skF_3')
      | ~ v1_partfun1('#skF_2'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_79)),'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1('#skF_2'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_79)))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_79)
      | '#skF_1'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_79)) = A_1
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_79) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_218,c_3072])).

tff(c_3090,plain,(
    ! [A_2898,C_2899] :
      ( '#skF_2'(A_2898,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2899)) = '#skF_6'
      | ~ v1_partfun1('#skF_2'(A_2898,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2899)),'#skF_3')
      | ~ v1_funct_1('#skF_2'(A_2898,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2899)))
      | ~ m1_subset_1(C_2899,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_2899)
      | '#skF_1'(A_2898,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2899)) = A_2898
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2899) = k1_tarski(A_2898) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_199,c_3076])).

tff(c_3094,plain,(
    ! [A_1,C_75] :
      ( '#skF_2'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_75)) = '#skF_6'
      | k1_tarski('#skF_4') = k1_xboole_0
      | ~ v1_funct_1('#skF_2'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_75)))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_75)
      | '#skF_1'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_75)) = A_1
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_75) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_2987,c_3090])).

tff(c_3098,plain,(
    ! [A_2900,C_2901] :
      ( '#skF_2'(A_2900,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2901)) = '#skF_6'
      | ~ v1_funct_1('#skF_2'(A_2900,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2901)))
      | ~ m1_subset_1(C_2901,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_2901)
      | '#skF_1'(A_2900,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2901)) = A_2900
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_2901) = k1_tarski(A_2900) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2777,c_3094])).

tff(c_3105,plain,(
    ! [A_2778] :
      ( '#skF_2'(A_2778,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = '#skF_6'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1('#skF_5')
      | '#skF_1'(A_2778,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = A_2778
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski(A_2778) ) ),
    inference(resolution,[status(thm)],[c_2832,c_3098])).

tff(c_3112,plain,(
    ! [A_2778] :
      ( '#skF_2'(A_2778,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = '#skF_6'
      | '#skF_1'(A_2778,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = A_2778
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski(A_2778) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3105])).

tff(c_3188,plain,(
    ! [A_2903] :
      ( '#skF_2'(A_2903,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = '#skF_6'
      | '#skF_1'(A_2903,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = A_2903
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski(A_2903) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3105])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3231,plain,(
    ! [A_2903] :
      ( '#skF_1'(A_2903,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = A_2903
      | A_2903 != '#skF_6'
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski(A_2903)
      | '#skF_1'(A_2903,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = A_2903
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski(A_2903) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3188,c_8])).

tff(c_3493,plain,(
    ! [A_2925] :
      ( A_2925 != '#skF_6'
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski(A_2925)
      | '#skF_1'(A_2925,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = A_2925 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3231])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3594,plain,(
    ! [A_2930] :
      ( ~ r2_hidden(A_2930,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5'))
      | '#skF_2'(A_2930,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) != A_2930
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski(A_2930)
      | A_2930 != '#skF_6'
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski(A_2930) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3493,c_6])).

tff(c_3601,plain,
    ( '#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) != '#skF_6'
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_2787,c_3594])).

tff(c_3616,plain,(
    '#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_3601])).

tff(c_3621,plain,
    ( '#skF_1'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = '#skF_6'
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3112,c_3616])).

tff(c_3624,plain,(
    '#skF_1'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3621])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_152,plain,(
    ! [A_1,A_60,B_61,C_62] :
      ( v1_funct_1('#skF_2'(A_1,k5_partfun1(A_60,B_61,C_62)))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_1(C_62)
      | ~ r2_hidden('#skF_1'(A_1,k5_partfun1(A_60,B_61,C_62)),k5_partfun1(A_60,B_61,C_62))
      | k5_partfun1(A_60,B_61,C_62) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_145])).

tff(c_3654,plain,
    ( v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
    | ~ v1_funct_1('#skF_5')
    | ~ r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5'))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3624,c_152])).

tff(c_3674,plain,
    ( v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2787,c_56,c_54,c_3654])).

tff(c_3675,plain,(
    v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3674])).

tff(c_207,plain,(
    ! [A_1,A_73,B_74,C_75] :
      ( v1_funct_2('#skF_2'(A_1,k5_partfun1(A_73,B_74,C_75)),A_73,B_74)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_1(C_75)
      | ~ r2_hidden('#skF_1'(A_1,k5_partfun1(A_73,B_74,C_75)),k5_partfun1(A_73,B_74,C_75))
      | k5_partfun1(A_73,B_74,C_75) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_200])).

tff(c_3651,plain,
    ( v1_funct_2('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),'#skF_3',k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
    | ~ v1_funct_1('#skF_5')
    | ~ r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5'))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3624,c_207])).

tff(c_3671,plain,
    ( v1_funct_2('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),'#skF_3',k1_tarski('#skF_4'))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2787,c_56,c_54,c_3651])).

tff(c_3672,plain,(
    v1_funct_2('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),'#skF_3',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3671])).

tff(c_217,plain,(
    ! [A_1,A_77,B_78,C_79] :
      ( m1_subset_1('#skF_2'(A_1,k5_partfun1(A_77,B_78,C_79)),k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_1(C_79)
      | ~ r2_hidden('#skF_1'(A_1,k5_partfun1(A_77,B_78,C_79)),k5_partfun1(A_77,B_78,C_79))
      | k5_partfun1(A_77,B_78,C_79) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_210])).

tff(c_3648,plain,
    ( m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
    | ~ v1_funct_1('#skF_5')
    | ~ r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5'))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3624,c_217])).

tff(c_3668,plain,
    ( m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2787,c_56,c_54,c_3648])).

tff(c_3669,plain,(
    m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3668])).

tff(c_3722,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),'#skF_3')
    | ~ v1_funct_2('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),'#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(resolution,[status(thm)],[c_3669,c_30])).

tff(c_3755,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3675,c_3672,c_3722])).

tff(c_3756,plain,(
    v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2777,c_3755])).

tff(c_3714,plain,
    ( r1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),'#skF_6')
    | ~ v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(resolution,[status(thm)],[c_3669,c_232])).

tff(c_3746,plain,(
    r1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3675,c_3714])).

tff(c_3760,plain,(
    ! [A_21,B_22] :
      ( '#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_21)
      | ~ v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),A_21)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_3746,c_34])).

tff(c_3766,plain,(
    ! [A_21,B_22] :
      ( '#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')) = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_21)
      | ~ v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),A_21)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3675,c_52,c_3760])).

tff(c_3830,plain,(
    ! [A_2937,B_2938] :
      ( ~ v1_partfun1('#skF_6',A_2937)
      | ~ v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),A_2937)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_2937,B_2938)))
      | ~ m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),k1_zfmisc_1(k2_zfmisc_1(A_2937,B_2938))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3616,c_3766])).

tff(c_3833,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_5')),'#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_3669,c_3830])).

tff(c_3854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3756,c_199,c_3833])).

tff(c_3855,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_182,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_179])).

tff(c_194,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_182])).

tff(c_209,plain,(
    ~ v1_funct_2('#skF_5','#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_3860,plain,(
    ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3855,c_209])).

tff(c_3869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3860])).

tff(c_3870,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_3872,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3870])).

tff(c_3891,plain,(
    ! [A_11] :
      ( k2_zfmisc_1(A_11,k1_xboole_0) != k1_xboole_0
      | k1_xboole_0 = A_11 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3872,c_24])).

tff(c_3906,plain,(
    ! [A_11] : k1_xboole_0 = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3891])).

tff(c_3876,plain,(
    k5_partfun1('#skF_3',k1_xboole_0,'#skF_5') != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3872,c_46])).

tff(c_4453,plain,(
    k1_tarski('#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3906,c_3876])).

tff(c_4471,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3906,c_4453])).

tff(c_4473,plain,(
    k1_tarski('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3870])).

tff(c_4472,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3870])).

tff(c_4483,plain,(
    ! [C_5924,D_5925,A_5926,B_5927] :
      ( r1_partfun1(C_5924,D_5925)
      | ~ m1_subset_1(D_5925,k1_zfmisc_1(k2_zfmisc_1(A_5926,k1_tarski(B_5927))))
      | ~ v1_funct_1(D_5925)
      | ~ m1_subset_1(C_5924,k1_zfmisc_1(k2_zfmisc_1(A_5926,k1_tarski(B_5927))))
      | ~ v1_funct_1(C_5924) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4487,plain,(
    ! [C_5924] :
      ( r1_partfun1(C_5924,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_5924,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_5924) ) ),
    inference(resolution,[status(thm)],[c_48,c_4483])).

tff(c_4529,plain,(
    ! [C_5932] :
      ( r1_partfun1(C_5932,'#skF_6')
      | ~ m1_subset_1(C_5932,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_5932) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4487])).

tff(c_4532,plain,
    ( r1_partfun1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_4529])).

tff(c_4538,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4532])).

tff(c_4543,plain,(
    ! [D_5935,C_5936,A_5937,B_5938] :
      ( D_5935 = C_5936
      | ~ r1_partfun1(C_5936,D_5935)
      | ~ v1_partfun1(D_5935,A_5937)
      | ~ v1_partfun1(C_5936,A_5937)
      | ~ m1_subset_1(D_5935,k1_zfmisc_1(k2_zfmisc_1(A_5937,B_5938)))
      | ~ v1_funct_1(D_5935)
      | ~ m1_subset_1(C_5936,k1_zfmisc_1(k2_zfmisc_1(A_5937,B_5938)))
      | ~ v1_funct_1(C_5936) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4547,plain,(
    ! [A_5937,B_5938] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_5937)
      | ~ v1_partfun1('#skF_5',A_5937)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_5937,B_5938)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_5937,B_5938)))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4538,c_4543])).

tff(c_4558,plain,(
    ! [A_5937,B_5938] :
      ( '#skF_5' = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_5937)
      | ~ v1_partfun1('#skF_5',A_5937)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_5937,B_5938)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_5937,B_5938))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_4547])).

tff(c_4587,plain,(
    ! [A_5943,B_5944] :
      ( ~ v1_partfun1('#skF_6',A_5943)
      | ~ v1_partfun1('#skF_5',A_5943)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_5943,B_5944)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_5943,B_5944))) ) ),
    inference(splitLeft,[status(thm)],[c_4558])).

tff(c_4590,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_54,c_4587])).

tff(c_4600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4472,c_199,c_4590])).

tff(c_4601,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4558])).

tff(c_4609,plain,(
    k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4601,c_46])).

tff(c_4535,plain,
    ( r1_partfun1('#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_4529])).

tff(c_4541,plain,(
    r1_partfun1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4535])).

tff(c_4642,plain,(
    ! [B_5960,D_5961,A_5962,C_5963] :
      ( k1_xboole_0 = B_5960
      | r2_hidden(D_5961,k5_partfun1(A_5962,B_5960,C_5963))
      | ~ r1_partfun1(C_5963,D_5961)
      | ~ m1_subset_1(D_5961,k1_zfmisc_1(k2_zfmisc_1(A_5962,B_5960)))
      | ~ v1_funct_2(D_5961,A_5962,B_5960)
      | ~ v1_funct_1(D_5961)
      | ~ m1_subset_1(C_5963,k1_zfmisc_1(k2_zfmisc_1(A_5962,B_5960)))
      | ~ v1_funct_1(C_5963) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4644,plain,(
    ! [C_5963] :
      ( k1_tarski('#skF_4') = k1_xboole_0
      | r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5963))
      | ~ r1_partfun1(C_5963,'#skF_6')
      | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(C_5963,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_5963) ) ),
    inference(resolution,[status(thm)],[c_48,c_4642])).

tff(c_4651,plain,(
    ! [C_5963] :
      ( k1_tarski('#skF_4') = k1_xboole_0
      | r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5963))
      | ~ r1_partfun1(C_5963,'#skF_6')
      | ~ m1_subset_1(C_5963,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_5963) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4644])).

tff(c_4656,plain,(
    ! [C_5964] :
      ( r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5964))
      | ~ r1_partfun1(C_5964,'#skF_6')
      | ~ m1_subset_1(C_5964,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_5964) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4473,c_4651])).

tff(c_4659,plain,
    ( r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6'))
    | ~ r1_partfun1('#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_4656])).

tff(c_4662,plain,(
    r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4541,c_4659])).

tff(c_4623,plain,(
    ! [A_5945,A_5946,B_5947,C_5948] :
      ( v1_funct_1('#skF_2'(A_5945,k5_partfun1(A_5946,B_5947,C_5948)))
      | ~ m1_subset_1(C_5948,k1_zfmisc_1(k2_zfmisc_1(A_5946,B_5947)))
      | ~ v1_funct_1(C_5948)
      | '#skF_1'(A_5945,k5_partfun1(A_5946,B_5947,C_5948)) = A_5945
      | k5_partfun1(A_5946,B_5947,C_5948) = k1_tarski(A_5945) ) ),
    inference(resolution,[status(thm)],[c_12,c_145])).

tff(c_4625,plain,(
    ! [A_5945] :
      ( v1_funct_1('#skF_2'(A_5945,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')))
      | ~ v1_funct_1('#skF_6')
      | '#skF_1'(A_5945,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = A_5945
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski(A_5945) ) ),
    inference(resolution,[status(thm)],[c_48,c_4623])).

tff(c_4632,plain,(
    ! [A_5945] :
      ( v1_funct_1('#skF_2'(A_5945,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')))
      | '#skF_1'(A_5945,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = A_5945
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski(A_5945) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4625])).

tff(c_4474,plain,(
    ! [D_5920,A_5921,B_5922,C_5923] :
      ( m1_subset_1(D_5920,k1_zfmisc_1(k2_zfmisc_1(A_5921,B_5922)))
      | ~ r2_hidden(D_5920,k5_partfun1(A_5921,B_5922,C_5923))
      | ~ m1_subset_1(C_5923,k1_zfmisc_1(k2_zfmisc_1(A_5921,B_5922)))
      | ~ v1_funct_1(C_5923) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4678,plain,(
    ! [A_5965,A_5966,B_5967,C_5968] :
      ( m1_subset_1('#skF_2'(A_5965,k5_partfun1(A_5966,B_5967,C_5968)),k1_zfmisc_1(k2_zfmisc_1(A_5966,B_5967)))
      | ~ m1_subset_1(C_5968,k1_zfmisc_1(k2_zfmisc_1(A_5966,B_5967)))
      | ~ v1_funct_1(C_5968)
      | '#skF_1'(A_5965,k5_partfun1(A_5966,B_5967,C_5968)) = A_5965
      | k5_partfun1(A_5966,B_5967,C_5968) = k1_tarski(A_5965) ) ),
    inference(resolution,[status(thm)],[c_12,c_4474])).

tff(c_4778,plain,(
    ! [B_6008,A_6009,A_6010,C_6011] :
      ( k1_xboole_0 = B_6008
      | v1_partfun1('#skF_2'(A_6009,k5_partfun1(A_6010,B_6008,C_6011)),A_6010)
      | ~ v1_funct_2('#skF_2'(A_6009,k5_partfun1(A_6010,B_6008,C_6011)),A_6010,B_6008)
      | ~ v1_funct_1('#skF_2'(A_6009,k5_partfun1(A_6010,B_6008,C_6011)))
      | ~ m1_subset_1(C_6011,k1_zfmisc_1(k2_zfmisc_1(A_6010,B_6008)))
      | ~ v1_funct_1(C_6011)
      | '#skF_1'(A_6009,k5_partfun1(A_6010,B_6008,C_6011)) = A_6009
      | k5_partfun1(A_6010,B_6008,C_6011) = k1_tarski(A_6009) ) ),
    inference(resolution,[status(thm)],[c_4678,c_30])).

tff(c_4782,plain,(
    ! [B_74,A_1,A_73,C_75] :
      ( k1_xboole_0 = B_74
      | v1_partfun1('#skF_2'(A_1,k5_partfun1(A_73,B_74,C_75)),A_73)
      | ~ v1_funct_1('#skF_2'(A_1,k5_partfun1(A_73,B_74,C_75)))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_1(C_75)
      | '#skF_1'(A_1,k5_partfun1(A_73,B_74,C_75)) = A_1
      | k5_partfun1(A_73,B_74,C_75) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_208,c_4778])).

tff(c_4482,plain,(
    ! [A_1,A_5921,B_5922,C_5923] :
      ( m1_subset_1('#skF_2'(A_1,k5_partfun1(A_5921,B_5922,C_5923)),k1_zfmisc_1(k2_zfmisc_1(A_5921,B_5922)))
      | ~ m1_subset_1(C_5923,k1_zfmisc_1(k2_zfmisc_1(A_5921,B_5922)))
      | ~ v1_funct_1(C_5923)
      | '#skF_1'(A_1,k5_partfun1(A_5921,B_5922,C_5923)) = A_1
      | k5_partfun1(A_5921,B_5922,C_5923) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_4474])).

tff(c_4496,plain,(
    ! [C_5924] :
      ( r1_partfun1(C_5924,'#skF_6')
      | ~ m1_subset_1(C_5924,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_5924) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4487])).

tff(c_4711,plain,(
    ! [A_5969,C_5970] :
      ( r1_partfun1('#skF_2'(A_5969,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5970)),'#skF_6')
      | ~ v1_funct_1('#skF_2'(A_5969,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5970)))
      | ~ m1_subset_1(C_5970,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_5970)
      | '#skF_1'(A_5969,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5970)) = A_5969
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5970) = k1_tarski(A_5969) ) ),
    inference(resolution,[status(thm)],[c_4678,c_4496])).

tff(c_4713,plain,(
    ! [A_5969,C_5970,A_21,B_22] :
      ( '#skF_2'(A_5969,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5970)) = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_21)
      | ~ v1_partfun1('#skF_2'(A_5969,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5970)),A_21)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_2'(A_5969,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5970)),k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1('#skF_2'(A_5969,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5970)))
      | ~ m1_subset_1(C_5970,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_5970)
      | '#skF_1'(A_5969,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5970)) = A_5969
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5970) = k1_tarski(A_5969) ) ),
    inference(resolution,[status(thm)],[c_4711,c_34])).

tff(c_4792,plain,(
    ! [A_6035,C_6036,A_6037,B_6038] :
      ( '#skF_2'(A_6035,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6036)) = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_6037)
      | ~ v1_partfun1('#skF_2'(A_6035,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6036)),A_6037)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_6037,B_6038)))
      | ~ m1_subset_1('#skF_2'(A_6035,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6036)),k1_zfmisc_1(k2_zfmisc_1(A_6037,B_6038)))
      | ~ v1_funct_1('#skF_2'(A_6035,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6036)))
      | ~ m1_subset_1(C_6036,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_6036)
      | '#skF_1'(A_6035,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6036)) = A_6035
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6036) = k1_tarski(A_6035) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4713])).

tff(c_4796,plain,(
    ! [A_1,C_5923] :
      ( '#skF_2'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5923)) = '#skF_6'
      | ~ v1_partfun1('#skF_6','#skF_3')
      | ~ v1_partfun1('#skF_2'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5923)),'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1('#skF_2'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5923)))
      | ~ m1_subset_1(C_5923,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_5923)
      | '#skF_1'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5923)) = A_1
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_5923) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_4482,c_4792])).

tff(c_4808,plain,(
    ! [A_6039,C_6040] :
      ( '#skF_2'(A_6039,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6040)) = '#skF_6'
      | ~ v1_partfun1('#skF_2'(A_6039,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6040)),'#skF_3')
      | ~ v1_funct_1('#skF_2'(A_6039,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6040)))
      | ~ m1_subset_1(C_6040,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_6040)
      | '#skF_1'(A_6039,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6040)) = A_6039
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6040) = k1_tarski(A_6039) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_199,c_4796])).

tff(c_4812,plain,(
    ! [A_1,C_75] :
      ( '#skF_2'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_75)) = '#skF_6'
      | k1_tarski('#skF_4') = k1_xboole_0
      | ~ v1_funct_1('#skF_2'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_75)))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_75)
      | '#skF_1'(A_1,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_75)) = A_1
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_75) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_4782,c_4808])).

tff(c_4816,plain,(
    ! [A_6041,C_6042] :
      ( '#skF_2'(A_6041,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6042)) = '#skF_6'
      | ~ v1_funct_1('#skF_2'(A_6041,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6042)))
      | ~ m1_subset_1(C_6042,k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1(C_6042)
      | '#skF_1'(A_6041,k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6042)) = A_6041
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),C_6042) = k1_tarski(A_6041) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4473,c_4812])).

tff(c_4821,plain,(
    ! [A_5945] :
      ( '#skF_2'(A_5945,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
      | ~ v1_funct_1('#skF_6')
      | '#skF_1'(A_5945,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = A_5945
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski(A_5945) ) ),
    inference(resolution,[status(thm)],[c_4632,c_4816])).

tff(c_4825,plain,(
    ! [A_5945] :
      ( '#skF_2'(A_5945,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = '#skF_6'
      | '#skF_1'(A_5945,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = A_5945
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski(A_5945) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_4821])).

tff(c_4827,plain,(
    ! [A_6043] :
      ( '#skF_2'(A_6043,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = '#skF_6'
      | '#skF_1'(A_6043,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = A_6043
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski(A_6043) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_4821])).

tff(c_4864,plain,(
    ! [A_6043] :
      ( '#skF_1'(A_6043,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = A_6043
      | A_6043 != '#skF_6'
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski(A_6043)
      | '#skF_1'(A_6043,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = A_6043
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski(A_6043) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4827,c_8])).

tff(c_4922,plain,(
    ! [A_6045] :
      ( A_6045 != '#skF_6'
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski(A_6045)
      | '#skF_1'(A_6045,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = A_6045 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4864])).

tff(c_5022,plain,(
    ! [A_6056] :
      ( ~ r2_hidden(A_6056,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6'))
      | '#skF_2'(A_6056,k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) != A_6056
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski(A_6056)
      | A_6056 != '#skF_6'
      | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski(A_6056) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4922,c_6])).

tff(c_5029,plain,
    ( '#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) != '#skF_6'
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_4662,c_5022])).

tff(c_5044,plain,(
    '#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_4609,c_4609,c_5029])).

tff(c_5049,plain,
    ( '#skF_1'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = '#skF_6'
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4825,c_5044])).

tff(c_5052,plain,(
    '#skF_1'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_4609,c_5049])).

tff(c_5064,plain,
    ( v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
    | ~ v1_funct_1('#skF_6')
    | ~ r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6'))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5052,c_152])).

tff(c_5084,plain,
    ( v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4662,c_52,c_48,c_5064])).

tff(c_5085,plain,(
    v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4609,c_5084])).

tff(c_5061,plain,
    ( v1_funct_2('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_3',k1_tarski('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
    | ~ v1_funct_1('#skF_6')
    | ~ r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6'))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5052,c_207])).

tff(c_5081,plain,
    ( v1_funct_2('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_3',k1_tarski('#skF_4'))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4662,c_52,c_48,c_5061])).

tff(c_5082,plain,(
    v1_funct_2('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_3',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_4609,c_5081])).

tff(c_4481,plain,(
    ! [A_1,A_5921,B_5922,C_5923] :
      ( m1_subset_1('#skF_2'(A_1,k5_partfun1(A_5921,B_5922,C_5923)),k1_zfmisc_1(k2_zfmisc_1(A_5921,B_5922)))
      | ~ m1_subset_1(C_5923,k1_zfmisc_1(k2_zfmisc_1(A_5921,B_5922)))
      | ~ v1_funct_1(C_5923)
      | ~ r2_hidden('#skF_1'(A_1,k5_partfun1(A_5921,B_5922,C_5923)),k5_partfun1(A_5921,B_5922,C_5923))
      | k5_partfun1(A_5921,B_5922,C_5923) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_4474])).

tff(c_5058,plain,
    ( m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
    | ~ v1_funct_1('#skF_6')
    | ~ r2_hidden('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6'))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5052,c_4481])).

tff(c_5078,plain,
    ( m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))))
    | k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4662,c_52,c_48,c_5058])).

tff(c_5079,plain,(
    m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_4609,c_5078])).

tff(c_5146,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_3')
    | ~ v1_funct_2('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6'))) ),
    inference(resolution,[status(thm)],[c_5079,c_30])).

tff(c_5172,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5085,c_5082,c_5146])).

tff(c_5173,plain,(
    v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_4473,c_5172])).

tff(c_5141,plain,
    ( r1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_6')
    | ~ v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6'))) ),
    inference(resolution,[status(thm)],[c_5079,c_4496])).

tff(c_5166,plain,(
    r1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5085,c_5141])).

tff(c_5177,plain,(
    ! [A_21,B_22] :
      ( '#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_21)
      | ~ v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),A_21)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_5166,c_34])).

tff(c_5183,plain,(
    ! [A_21,B_22] :
      ( '#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')) = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_21)
      | ~ v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),A_21)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5085,c_52,c_5177])).

tff(c_5187,plain,(
    ! [A_6064,B_6065] :
      ( ~ v1_partfun1('#skF_6',A_6064)
      | ~ v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),A_6064)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_6064,B_6065)))
      | ~ m1_subset_1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),k1_zfmisc_1(k2_zfmisc_1(A_6064,B_6065))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5044,c_5183])).

tff(c_5190,plain,
    ( ~ v1_partfun1('#skF_6','#skF_3')
    | ~ v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_5079,c_5187])).

tff(c_5210,plain,(
    ~ v1_partfun1('#skF_2'('#skF_6',k5_partfun1('#skF_3',k1_tarski('#skF_4'),'#skF_6')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_199,c_5190])).

tff(c_5229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5173,c_5210])).

tff(c_5230,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_5249,plain,(
    ! [A_11] :
      ( k2_zfmisc_1(A_11,k1_xboole_0) != k1_xboole_0
      | k1_xboole_0 = A_11 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5230,c_24])).

tff(c_5264,plain,(
    ! [A_11] : k1_xboole_0 = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5249])).

tff(c_5234,plain,(
    k5_partfun1('#skF_3',k1_xboole_0,'#skF_5') != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5230,c_46])).

tff(c_5814,plain,(
    k1_tarski('#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5264,c_5234])).

tff(c_5832,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5264,c_5814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.34  % Computer   : n013.cluster.edu
% 0.11/0.34  % Model      : x86_64 x86_64
% 0.11/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.34  % Memory     : 8042.1875MB
% 0.11/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.34  % CPULimit   : 60
% 0.11/0.34  % DateTime   : Tue Dec  1 17:43:54 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.64/2.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.67  
% 7.95/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.68  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.95/2.68  
% 7.95/2.68  %Foreground sorts:
% 7.95/2.68  
% 7.95/2.68  
% 7.95/2.68  %Background operators:
% 7.95/2.68  
% 7.95/2.68  
% 7.95/2.68  %Foreground operators:
% 7.95/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.95/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.95/2.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.95/2.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.95/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.95/2.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.95/2.68  tff('#skF_5', type, '#skF_5': $i).
% 7.95/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.95/2.68  tff('#skF_6', type, '#skF_6': $i).
% 7.95/2.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.95/2.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.95/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.95/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.95/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.95/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.95/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.95/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.95/2.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.95/2.68  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 7.95/2.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.95/2.68  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 7.95/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.95/2.68  
% 7.95/2.71  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.95/2.71  tff(f_143, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (k5_partfun1(A, k1_tarski(B), C) = k1_tarski(D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_2)).
% 7.95/2.71  tff(f_68, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 7.95/2.71  tff(f_116, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 7.95/2.71  tff(f_51, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 7.95/2.71  tff(f_79, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => r1_partfun1(C, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_partfun1)).
% 7.95/2.71  tff(f_96, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 7.95/2.71  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.95/2.71  tff(f_129, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (r2_hidden(D, k5_partfun1(A, B, C)) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 7.95/2.71  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.95/2.71  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.95/2.71  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.95/2.71  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.95/2.71  tff(c_179, plain, (![B_69, C_70, A_71]: (k1_xboole_0=B_69 | v1_partfun1(C_70, A_71) | ~v1_funct_2(C_70, A_71, B_69) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_69))) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.95/2.71  tff(c_185, plain, (k1_tarski('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_6', '#skF_3') | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_179])).
% 7.95/2.71  tff(c_197, plain, (k1_tarski('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_185])).
% 7.95/2.71  tff(c_199, plain, (v1_partfun1('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_197])).
% 7.95/2.71  tff(c_2189, plain, (![B_363, D_364, A_365, C_366]: (k1_xboole_0=B_363 | r2_hidden(D_364, k5_partfun1(A_365, B_363, C_366)) | ~r1_partfun1(C_366, D_364) | ~m1_subset_1(D_364, k1_zfmisc_1(k2_zfmisc_1(A_365, B_363))) | ~v1_funct_2(D_364, A_365, B_363) | ~v1_funct_1(D_364) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_365, B_363))) | ~v1_funct_1(C_366))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.95/2.71  tff(c_2193, plain, (![C_366]: (k1_tarski('#skF_4')=k1_xboole_0 | r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_366)) | ~r1_partfun1(C_366, '#skF_6') | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_366))), inference(resolution, [status(thm)], [c_48, c_2189])).
% 7.95/2.71  tff(c_2203, plain, (![C_366]: (k1_tarski('#skF_4')=k1_xboole_0 | r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_366)) | ~r1_partfun1(C_366, '#skF_6') | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_366))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2193])).
% 7.95/2.71  tff(c_2222, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2203])).
% 7.95/2.71  tff(c_24, plain, (![A_11, B_12]: (k2_zfmisc_1(A_11, k1_tarski(B_12))!=k1_xboole_0 | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.95/2.71  tff(c_2247, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)!=k1_xboole_0 | k1_xboole_0=A_11)), inference(superposition, [status(thm), theory('equality')], [c_2222, c_24])).
% 7.95/2.71  tff(c_2274, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2247])).
% 7.95/2.71  tff(c_2263, plain, (![A_11]: (k1_xboole_0=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2247])).
% 7.95/2.71  tff(c_2621, plain, (![A_2136]: (A_2136='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2274, c_2263])).
% 7.95/2.71  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.95/2.71  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.95/2.71  tff(c_219, plain, (![C_80, D_81, A_82, B_83]: (r1_partfun1(C_80, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_82, k1_tarski(B_83)))) | ~v1_funct_1(D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, k1_tarski(B_83)))) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.95/2.71  tff(c_223, plain, (![C_80]: (r1_partfun1(C_80, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_80))), inference(resolution, [status(thm)], [c_48, c_219])).
% 7.95/2.71  tff(c_247, plain, (![C_85]: (r1_partfun1(C_85, '#skF_6') | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_85))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_223])).
% 7.95/2.71  tff(c_250, plain, (r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_247])).
% 7.95/2.71  tff(c_256, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_250])).
% 7.95/2.71  tff(c_279, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r1_partfun1(C_92, D_91) | ~v1_partfun1(D_91, A_93) | ~v1_partfun1(C_92, A_93) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_1(D_91) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.95/2.71  tff(c_283, plain, (![A_93, B_94]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_93) | ~v1_partfun1('#skF_5', A_93) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_256, c_279])).
% 7.95/2.71  tff(c_294, plain, (![A_93, B_94]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_93) | ~v1_partfun1('#skF_5', A_93) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_283])).
% 7.95/2.71  tff(c_303, plain, (![A_95, B_96]: (~v1_partfun1('#skF_6', A_95) | ~v1_partfun1('#skF_5', A_95) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(splitLeft, [status(thm)], [c_294])).
% 7.95/2.71  tff(c_306, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(resolution, [status(thm)], [c_54, c_303])).
% 7.95/2.71  tff(c_315, plain, (~v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_199, c_306])).
% 7.95/2.71  tff(c_2667, plain, (~v1_partfun1('#skF_6', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2621, c_315])).
% 7.95/2.71  tff(c_2775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_2667])).
% 7.95/2.71  tff(c_2777, plain, (k1_tarski('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2203])).
% 7.95/2.71  tff(c_46, plain, (k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.95/2.71  tff(c_2778, plain, (![C_2777]: (r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2777)) | ~r1_partfun1(C_2777, '#skF_6') | ~m1_subset_1(C_2777, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_2777))), inference(splitRight, [status(thm)], [c_2203])).
% 7.95/2.71  tff(c_2781, plain, (r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')) | ~r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_2778])).
% 7.95/2.71  tff(c_2787, plain, (r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_256, c_2781])).
% 7.95/2.71  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.95/2.71  tff(c_145, plain, (![D_59, A_60, B_61, C_62]: (v1_funct_1(D_59) | ~r2_hidden(D_59, k5_partfun1(A_60, B_61, C_62)) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_1(C_62))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.95/2.71  tff(c_2821, plain, (![A_2778, A_2779, B_2780, C_2781]: (v1_funct_1('#skF_2'(A_2778, k5_partfun1(A_2779, B_2780, C_2781))) | ~m1_subset_1(C_2781, k1_zfmisc_1(k2_zfmisc_1(A_2779, B_2780))) | ~v1_funct_1(C_2781) | '#skF_1'(A_2778, k5_partfun1(A_2779, B_2780, C_2781))=A_2778 | k5_partfun1(A_2779, B_2780, C_2781)=k1_tarski(A_2778))), inference(resolution, [status(thm)], [c_12, c_145])).
% 7.95/2.71  tff(c_2823, plain, (![A_2778]: (v1_funct_1('#skF_2'(A_2778, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))) | ~v1_funct_1('#skF_5') | '#skF_1'(A_2778, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))=A_2778 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski(A_2778))), inference(resolution, [status(thm)], [c_54, c_2821])).
% 7.95/2.71  tff(c_2832, plain, (![A_2778]: (v1_funct_1('#skF_2'(A_2778, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))) | '#skF_1'(A_2778, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))=A_2778 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski(A_2778))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2823])).
% 7.95/2.71  tff(c_200, plain, (![D_72, A_73, B_74, C_75]: (v1_funct_2(D_72, A_73, B_74) | ~r2_hidden(D_72, k5_partfun1(A_73, B_74, C_75)) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_1(C_75))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.95/2.71  tff(c_208, plain, (![A_1, A_73, B_74, C_75]: (v1_funct_2('#skF_2'(A_1, k5_partfun1(A_73, B_74, C_75)), A_73, B_74) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_1(C_75) | '#skF_1'(A_1, k5_partfun1(A_73, B_74, C_75))=A_1 | k5_partfun1(A_73, B_74, C_75)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_12, c_200])).
% 7.95/2.71  tff(c_210, plain, (![D_76, A_77, B_78, C_79]: (m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~r2_hidden(D_76, k5_partfun1(A_77, B_78, C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.95/2.71  tff(c_2853, plain, (![A_2798, A_2799, B_2800, C_2801]: (m1_subset_1('#skF_2'(A_2798, k5_partfun1(A_2799, B_2800, C_2801)), k1_zfmisc_1(k2_zfmisc_1(A_2799, B_2800))) | ~m1_subset_1(C_2801, k1_zfmisc_1(k2_zfmisc_1(A_2799, B_2800))) | ~v1_funct_1(C_2801) | '#skF_1'(A_2798, k5_partfun1(A_2799, B_2800, C_2801))=A_2798 | k5_partfun1(A_2799, B_2800, C_2801)=k1_tarski(A_2798))), inference(resolution, [status(thm)], [c_12, c_210])).
% 7.95/2.71  tff(c_30, plain, (![B_14, C_15, A_13]: (k1_xboole_0=B_14 | v1_partfun1(C_15, A_13) | ~v1_funct_2(C_15, A_13, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.95/2.71  tff(c_2983, plain, (![B_2846, A_2847, A_2848, C_2849]: (k1_xboole_0=B_2846 | v1_partfun1('#skF_2'(A_2847, k5_partfun1(A_2848, B_2846, C_2849)), A_2848) | ~v1_funct_2('#skF_2'(A_2847, k5_partfun1(A_2848, B_2846, C_2849)), A_2848, B_2846) | ~v1_funct_1('#skF_2'(A_2847, k5_partfun1(A_2848, B_2846, C_2849))) | ~m1_subset_1(C_2849, k1_zfmisc_1(k2_zfmisc_1(A_2848, B_2846))) | ~v1_funct_1(C_2849) | '#skF_1'(A_2847, k5_partfun1(A_2848, B_2846, C_2849))=A_2847 | k5_partfun1(A_2848, B_2846, C_2849)=k1_tarski(A_2847))), inference(resolution, [status(thm)], [c_2853, c_30])).
% 7.95/2.71  tff(c_2987, plain, (![B_74, A_1, A_73, C_75]: (k1_xboole_0=B_74 | v1_partfun1('#skF_2'(A_1, k5_partfun1(A_73, B_74, C_75)), A_73) | ~v1_funct_1('#skF_2'(A_1, k5_partfun1(A_73, B_74, C_75))) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_1(C_75) | '#skF_1'(A_1, k5_partfun1(A_73, B_74, C_75))=A_1 | k5_partfun1(A_73, B_74, C_75)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_208, c_2983])).
% 7.95/2.71  tff(c_218, plain, (![A_1, A_77, B_78, C_79]: (m1_subset_1('#skF_2'(A_1, k5_partfun1(A_77, B_78, C_79)), k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(C_79) | '#skF_1'(A_1, k5_partfun1(A_77, B_78, C_79))=A_1 | k5_partfun1(A_77, B_78, C_79)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_12, c_210])).
% 7.95/2.71  tff(c_232, plain, (![C_80]: (r1_partfun1(C_80, '#skF_6') | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_80))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_223])).
% 7.95/2.71  tff(c_2891, plain, (![A_2802, C_2803]: (r1_partfun1('#skF_2'(A_2802, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2803)), '#skF_6') | ~v1_funct_1('#skF_2'(A_2802, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2803))) | ~m1_subset_1(C_2803, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_2803) | '#skF_1'(A_2802, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2803))=A_2802 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2803)=k1_tarski(A_2802))), inference(resolution, [status(thm)], [c_2853, c_232])).
% 7.95/2.71  tff(c_34, plain, (![D_25, C_23, A_21, B_22]: (D_25=C_23 | ~r1_partfun1(C_23, D_25) | ~v1_partfun1(D_25, A_21) | ~v1_partfun1(C_23, A_21) | ~m1_subset_1(D_25, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1(D_25) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.95/2.71  tff(c_2893, plain, (![A_2802, C_2803, A_21, B_22]: ('#skF_2'(A_2802, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2803))='#skF_6' | ~v1_partfun1('#skF_6', A_21) | ~v1_partfun1('#skF_2'(A_2802, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2803)), A_21) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_2'(A_2802, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2803)), k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1('#skF_2'(A_2802, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2803))) | ~m1_subset_1(C_2803, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_2803) | '#skF_1'(A_2802, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2803))=A_2802 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2803)=k1_tarski(A_2802))), inference(resolution, [status(thm)], [c_2891, c_34])).
% 7.95/2.71  tff(c_3072, plain, (![A_2894, C_2895, A_2896, B_2897]: ('#skF_2'(A_2894, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2895))='#skF_6' | ~v1_partfun1('#skF_6', A_2896) | ~v1_partfun1('#skF_2'(A_2894, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2895)), A_2896) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_2896, B_2897))) | ~m1_subset_1('#skF_2'(A_2894, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2895)), k1_zfmisc_1(k2_zfmisc_1(A_2896, B_2897))) | ~v1_funct_1('#skF_2'(A_2894, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2895))) | ~m1_subset_1(C_2895, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_2895) | '#skF_1'(A_2894, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2895))=A_2894 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2895)=k1_tarski(A_2894))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2893])).
% 7.95/2.71  tff(c_3076, plain, (![A_1, C_79]: ('#skF_2'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_79))='#skF_6' | ~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_2'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_79)), '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1('#skF_2'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_79))) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_79) | '#skF_1'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_79))=A_1 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_79)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_218, c_3072])).
% 7.95/2.71  tff(c_3090, plain, (![A_2898, C_2899]: ('#skF_2'(A_2898, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2899))='#skF_6' | ~v1_partfun1('#skF_2'(A_2898, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2899)), '#skF_3') | ~v1_funct_1('#skF_2'(A_2898, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2899))) | ~m1_subset_1(C_2899, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_2899) | '#skF_1'(A_2898, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2899))=A_2898 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2899)=k1_tarski(A_2898))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_199, c_3076])).
% 7.95/2.71  tff(c_3094, plain, (![A_1, C_75]: ('#skF_2'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_75))='#skF_6' | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_1('#skF_2'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_75))) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_75) | '#skF_1'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_75))=A_1 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_75)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_2987, c_3090])).
% 7.95/2.71  tff(c_3098, plain, (![A_2900, C_2901]: ('#skF_2'(A_2900, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2901))='#skF_6' | ~v1_funct_1('#skF_2'(A_2900, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2901))) | ~m1_subset_1(C_2901, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_2901) | '#skF_1'(A_2900, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2901))=A_2900 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_2901)=k1_tarski(A_2900))), inference(negUnitSimplification, [status(thm)], [c_2777, c_3094])).
% 7.95/2.71  tff(c_3105, plain, (![A_2778]: ('#skF_2'(A_2778, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))='#skF_6' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1('#skF_5') | '#skF_1'(A_2778, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))=A_2778 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski(A_2778))), inference(resolution, [status(thm)], [c_2832, c_3098])).
% 7.95/2.71  tff(c_3112, plain, (![A_2778]: ('#skF_2'(A_2778, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))='#skF_6' | '#skF_1'(A_2778, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))=A_2778 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski(A_2778))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3105])).
% 7.95/2.71  tff(c_3188, plain, (![A_2903]: ('#skF_2'(A_2903, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))='#skF_6' | '#skF_1'(A_2903, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))=A_2903 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski(A_2903))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3105])).
% 7.95/2.71  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.95/2.71  tff(c_3231, plain, (![A_2903]: ('#skF_1'(A_2903, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))=A_2903 | A_2903!='#skF_6' | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski(A_2903) | '#skF_1'(A_2903, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))=A_2903 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski(A_2903))), inference(superposition, [status(thm), theory('equality')], [c_3188, c_8])).
% 7.95/2.71  tff(c_3493, plain, (![A_2925]: (A_2925!='#skF_6' | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski(A_2925) | '#skF_1'(A_2925, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))=A_2925)), inference(factorization, [status(thm), theory('equality')], [c_3231])).
% 7.95/2.71  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.95/2.71  tff(c_3594, plain, (![A_2930]: (~r2_hidden(A_2930, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')) | '#skF_2'(A_2930, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))!=A_2930 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski(A_2930) | A_2930!='#skF_6' | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski(A_2930))), inference(superposition, [status(thm), theory('equality')], [c_3493, c_6])).
% 7.95/2.71  tff(c_3601, plain, ('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))!='#skF_6' | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_2787, c_3594])).
% 7.95/2.71  tff(c_3616, plain, ('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_3601])).
% 7.95/2.71  tff(c_3621, plain, ('#skF_1'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))='#skF_6' | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3112, c_3616])).
% 7.95/2.71  tff(c_3624, plain, ('#skF_1'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_46, c_3621])).
% 7.95/2.71  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.95/2.71  tff(c_152, plain, (![A_1, A_60, B_61, C_62]: (v1_funct_1('#skF_2'(A_1, k5_partfun1(A_60, B_61, C_62))) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_1(C_62) | ~r2_hidden('#skF_1'(A_1, k5_partfun1(A_60, B_61, C_62)), k5_partfun1(A_60, B_61, C_62)) | k5_partfun1(A_60, B_61, C_62)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_10, c_145])).
% 7.95/2.71  tff(c_3654, plain, (v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1('#skF_5') | ~r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3624, c_152])).
% 7.95/2.71  tff(c_3674, plain, (v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2787, c_56, c_54, c_3654])).
% 7.95/2.71  tff(c_3675, plain, (v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_46, c_3674])).
% 7.95/2.71  tff(c_207, plain, (![A_1, A_73, B_74, C_75]: (v1_funct_2('#skF_2'(A_1, k5_partfun1(A_73, B_74, C_75)), A_73, B_74) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_1(C_75) | ~r2_hidden('#skF_1'(A_1, k5_partfun1(A_73, B_74, C_75)), k5_partfun1(A_73, B_74, C_75)) | k5_partfun1(A_73, B_74, C_75)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_10, c_200])).
% 7.95/2.71  tff(c_3651, plain, (v1_funct_2('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), '#skF_3', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1('#skF_5') | ~r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3624, c_207])).
% 7.95/2.71  tff(c_3671, plain, (v1_funct_2('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), '#skF_3', k1_tarski('#skF_4')) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2787, c_56, c_54, c_3651])).
% 7.95/2.71  tff(c_3672, plain, (v1_funct_2('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), '#skF_3', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_3671])).
% 7.95/2.71  tff(c_217, plain, (![A_1, A_77, B_78, C_79]: (m1_subset_1('#skF_2'(A_1, k5_partfun1(A_77, B_78, C_79)), k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_1(C_79) | ~r2_hidden('#skF_1'(A_1, k5_partfun1(A_77, B_78, C_79)), k5_partfun1(A_77, B_78, C_79)) | k5_partfun1(A_77, B_78, C_79)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_10, c_210])).
% 7.95/2.71  tff(c_3648, plain, (m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1('#skF_5') | ~r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3624, c_217])).
% 7.95/2.71  tff(c_3668, plain, (m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2787, c_56, c_54, c_3648])).
% 7.95/2.71  tff(c_3669, plain, (m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_3668])).
% 7.95/2.71  tff(c_3722, plain, (k1_tarski('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), '#skF_3') | ~v1_funct_2('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')))), inference(resolution, [status(thm)], [c_3669, c_30])).
% 7.95/2.71  tff(c_3755, plain, (k1_tarski('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3675, c_3672, c_3722])).
% 7.95/2.71  tff(c_3756, plain, (v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2777, c_3755])).
% 7.95/2.71  tff(c_3714, plain, (r1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), '#skF_6') | ~v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')))), inference(resolution, [status(thm)], [c_3669, c_232])).
% 7.95/2.71  tff(c_3746, plain, (r1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3675, c_3714])).
% 7.95/2.71  tff(c_3760, plain, (![A_21, B_22]: ('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))='#skF_6' | ~v1_partfun1('#skF_6', A_21) | ~v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), A_21) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))))), inference(resolution, [status(thm)], [c_3746, c_34])).
% 7.95/2.71  tff(c_3766, plain, (![A_21, B_22]: ('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5'))='#skF_6' | ~v1_partfun1('#skF_6', A_21) | ~v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), A_21) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(demodulation, [status(thm), theory('equality')], [c_3675, c_52, c_3760])).
% 7.95/2.71  tff(c_3830, plain, (![A_2937, B_2938]: (~v1_partfun1('#skF_6', A_2937) | ~v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), A_2937) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_2937, B_2938))) | ~m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(A_2937, B_2938))))), inference(negUnitSimplification, [status(thm)], [c_3616, c_3766])).
% 7.95/2.71  tff(c_3833, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_5')), '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(resolution, [status(thm)], [c_3669, c_3830])).
% 7.95/2.71  tff(c_3854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_3756, c_199, c_3833])).
% 7.95/2.71  tff(c_3855, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_294])).
% 7.95/2.71  tff(c_182, plain, (k1_tarski('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_179])).
% 7.95/2.71  tff(c_194, plain, (k1_tarski('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_182])).
% 7.95/2.71  tff(c_209, plain, (~v1_funct_2('#skF_5', '#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_194])).
% 7.95/2.71  tff(c_3860, plain, (~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3855, c_209])).
% 7.95/2.71  tff(c_3869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3860])).
% 7.95/2.71  tff(c_3870, plain, (v1_partfun1('#skF_5', '#skF_3') | k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_194])).
% 7.95/2.71  tff(c_3872, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3870])).
% 7.95/2.71  tff(c_3891, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)!=k1_xboole_0 | k1_xboole_0=A_11)), inference(superposition, [status(thm), theory('equality')], [c_3872, c_24])).
% 7.95/2.71  tff(c_3906, plain, (![A_11]: (k1_xboole_0=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3891])).
% 7.95/2.71  tff(c_3876, plain, (k5_partfun1('#skF_3', k1_xboole_0, '#skF_5')!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3872, c_46])).
% 7.95/2.71  tff(c_4453, plain, (k1_tarski('#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3906, c_3876])).
% 7.95/2.71  tff(c_4471, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3906, c_4453])).
% 7.95/2.71  tff(c_4473, plain, (k1_tarski('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_3870])).
% 7.95/2.71  tff(c_4472, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_3870])).
% 7.95/2.71  tff(c_4483, plain, (![C_5924, D_5925, A_5926, B_5927]: (r1_partfun1(C_5924, D_5925) | ~m1_subset_1(D_5925, k1_zfmisc_1(k2_zfmisc_1(A_5926, k1_tarski(B_5927)))) | ~v1_funct_1(D_5925) | ~m1_subset_1(C_5924, k1_zfmisc_1(k2_zfmisc_1(A_5926, k1_tarski(B_5927)))) | ~v1_funct_1(C_5924))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.95/2.71  tff(c_4487, plain, (![C_5924]: (r1_partfun1(C_5924, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_5924, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_5924))), inference(resolution, [status(thm)], [c_48, c_4483])).
% 7.95/2.71  tff(c_4529, plain, (![C_5932]: (r1_partfun1(C_5932, '#skF_6') | ~m1_subset_1(C_5932, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_5932))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4487])).
% 7.95/2.71  tff(c_4532, plain, (r1_partfun1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_4529])).
% 7.95/2.71  tff(c_4538, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4532])).
% 7.95/2.71  tff(c_4543, plain, (![D_5935, C_5936, A_5937, B_5938]: (D_5935=C_5936 | ~r1_partfun1(C_5936, D_5935) | ~v1_partfun1(D_5935, A_5937) | ~v1_partfun1(C_5936, A_5937) | ~m1_subset_1(D_5935, k1_zfmisc_1(k2_zfmisc_1(A_5937, B_5938))) | ~v1_funct_1(D_5935) | ~m1_subset_1(C_5936, k1_zfmisc_1(k2_zfmisc_1(A_5937, B_5938))) | ~v1_funct_1(C_5936))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.95/2.71  tff(c_4547, plain, (![A_5937, B_5938]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_5937) | ~v1_partfun1('#skF_5', A_5937) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_5937, B_5938))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_5937, B_5938))) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_4538, c_4543])).
% 7.95/2.71  tff(c_4558, plain, (![A_5937, B_5938]: ('#skF_5'='#skF_6' | ~v1_partfun1('#skF_6', A_5937) | ~v1_partfun1('#skF_5', A_5937) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_5937, B_5938))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_5937, B_5938))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_4547])).
% 7.95/2.71  tff(c_4587, plain, (![A_5943, B_5944]: (~v1_partfun1('#skF_6', A_5943) | ~v1_partfun1('#skF_5', A_5943) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_5943, B_5944))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_5943, B_5944))))), inference(splitLeft, [status(thm)], [c_4558])).
% 7.95/2.71  tff(c_4590, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_5', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(resolution, [status(thm)], [c_54, c_4587])).
% 7.95/2.71  tff(c_4600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_4472, c_199, c_4590])).
% 7.95/2.71  tff(c_4601, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_4558])).
% 7.95/2.71  tff(c_4609, plain, (k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4601, c_46])).
% 7.95/2.71  tff(c_4535, plain, (r1_partfun1('#skF_6', '#skF_6') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_4529])).
% 7.95/2.71  tff(c_4541, plain, (r1_partfun1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4535])).
% 7.95/2.71  tff(c_4642, plain, (![B_5960, D_5961, A_5962, C_5963]: (k1_xboole_0=B_5960 | r2_hidden(D_5961, k5_partfun1(A_5962, B_5960, C_5963)) | ~r1_partfun1(C_5963, D_5961) | ~m1_subset_1(D_5961, k1_zfmisc_1(k2_zfmisc_1(A_5962, B_5960))) | ~v1_funct_2(D_5961, A_5962, B_5960) | ~v1_funct_1(D_5961) | ~m1_subset_1(C_5963, k1_zfmisc_1(k2_zfmisc_1(A_5962, B_5960))) | ~v1_funct_1(C_5963))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.95/2.71  tff(c_4644, plain, (![C_5963]: (k1_tarski('#skF_4')=k1_xboole_0 | r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5963)) | ~r1_partfun1(C_5963, '#skF_6') | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(C_5963, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_5963))), inference(resolution, [status(thm)], [c_48, c_4642])).
% 7.95/2.71  tff(c_4651, plain, (![C_5963]: (k1_tarski('#skF_4')=k1_xboole_0 | r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5963)) | ~r1_partfun1(C_5963, '#skF_6') | ~m1_subset_1(C_5963, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_5963))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4644])).
% 7.95/2.71  tff(c_4656, plain, (![C_5964]: (r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5964)) | ~r1_partfun1(C_5964, '#skF_6') | ~m1_subset_1(C_5964, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_5964))), inference(negUnitSimplification, [status(thm)], [c_4473, c_4651])).
% 7.95/2.71  tff(c_4659, plain, (r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')) | ~r1_partfun1('#skF_6', '#skF_6') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_4656])).
% 7.95/2.71  tff(c_4662, plain, (r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4541, c_4659])).
% 7.95/2.71  tff(c_4623, plain, (![A_5945, A_5946, B_5947, C_5948]: (v1_funct_1('#skF_2'(A_5945, k5_partfun1(A_5946, B_5947, C_5948))) | ~m1_subset_1(C_5948, k1_zfmisc_1(k2_zfmisc_1(A_5946, B_5947))) | ~v1_funct_1(C_5948) | '#skF_1'(A_5945, k5_partfun1(A_5946, B_5947, C_5948))=A_5945 | k5_partfun1(A_5946, B_5947, C_5948)=k1_tarski(A_5945))), inference(resolution, [status(thm)], [c_12, c_145])).
% 7.95/2.71  tff(c_4625, plain, (![A_5945]: (v1_funct_1('#skF_2'(A_5945, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))) | ~v1_funct_1('#skF_6') | '#skF_1'(A_5945, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))=A_5945 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski(A_5945))), inference(resolution, [status(thm)], [c_48, c_4623])).
% 7.95/2.71  tff(c_4632, plain, (![A_5945]: (v1_funct_1('#skF_2'(A_5945, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))) | '#skF_1'(A_5945, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))=A_5945 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski(A_5945))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4625])).
% 7.95/2.71  tff(c_4474, plain, (![D_5920, A_5921, B_5922, C_5923]: (m1_subset_1(D_5920, k1_zfmisc_1(k2_zfmisc_1(A_5921, B_5922))) | ~r2_hidden(D_5920, k5_partfun1(A_5921, B_5922, C_5923)) | ~m1_subset_1(C_5923, k1_zfmisc_1(k2_zfmisc_1(A_5921, B_5922))) | ~v1_funct_1(C_5923))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.95/2.71  tff(c_4678, plain, (![A_5965, A_5966, B_5967, C_5968]: (m1_subset_1('#skF_2'(A_5965, k5_partfun1(A_5966, B_5967, C_5968)), k1_zfmisc_1(k2_zfmisc_1(A_5966, B_5967))) | ~m1_subset_1(C_5968, k1_zfmisc_1(k2_zfmisc_1(A_5966, B_5967))) | ~v1_funct_1(C_5968) | '#skF_1'(A_5965, k5_partfun1(A_5966, B_5967, C_5968))=A_5965 | k5_partfun1(A_5966, B_5967, C_5968)=k1_tarski(A_5965))), inference(resolution, [status(thm)], [c_12, c_4474])).
% 7.95/2.71  tff(c_4778, plain, (![B_6008, A_6009, A_6010, C_6011]: (k1_xboole_0=B_6008 | v1_partfun1('#skF_2'(A_6009, k5_partfun1(A_6010, B_6008, C_6011)), A_6010) | ~v1_funct_2('#skF_2'(A_6009, k5_partfun1(A_6010, B_6008, C_6011)), A_6010, B_6008) | ~v1_funct_1('#skF_2'(A_6009, k5_partfun1(A_6010, B_6008, C_6011))) | ~m1_subset_1(C_6011, k1_zfmisc_1(k2_zfmisc_1(A_6010, B_6008))) | ~v1_funct_1(C_6011) | '#skF_1'(A_6009, k5_partfun1(A_6010, B_6008, C_6011))=A_6009 | k5_partfun1(A_6010, B_6008, C_6011)=k1_tarski(A_6009))), inference(resolution, [status(thm)], [c_4678, c_30])).
% 7.95/2.71  tff(c_4782, plain, (![B_74, A_1, A_73, C_75]: (k1_xboole_0=B_74 | v1_partfun1('#skF_2'(A_1, k5_partfun1(A_73, B_74, C_75)), A_73) | ~v1_funct_1('#skF_2'(A_1, k5_partfun1(A_73, B_74, C_75))) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_1(C_75) | '#skF_1'(A_1, k5_partfun1(A_73, B_74, C_75))=A_1 | k5_partfun1(A_73, B_74, C_75)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_208, c_4778])).
% 7.95/2.71  tff(c_4482, plain, (![A_1, A_5921, B_5922, C_5923]: (m1_subset_1('#skF_2'(A_1, k5_partfun1(A_5921, B_5922, C_5923)), k1_zfmisc_1(k2_zfmisc_1(A_5921, B_5922))) | ~m1_subset_1(C_5923, k1_zfmisc_1(k2_zfmisc_1(A_5921, B_5922))) | ~v1_funct_1(C_5923) | '#skF_1'(A_1, k5_partfun1(A_5921, B_5922, C_5923))=A_1 | k5_partfun1(A_5921, B_5922, C_5923)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_12, c_4474])).
% 7.95/2.71  tff(c_4496, plain, (![C_5924]: (r1_partfun1(C_5924, '#skF_6') | ~m1_subset_1(C_5924, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_5924))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4487])).
% 7.95/2.71  tff(c_4711, plain, (![A_5969, C_5970]: (r1_partfun1('#skF_2'(A_5969, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5970)), '#skF_6') | ~v1_funct_1('#skF_2'(A_5969, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5970))) | ~m1_subset_1(C_5970, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_5970) | '#skF_1'(A_5969, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5970))=A_5969 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5970)=k1_tarski(A_5969))), inference(resolution, [status(thm)], [c_4678, c_4496])).
% 7.95/2.71  tff(c_4713, plain, (![A_5969, C_5970, A_21, B_22]: ('#skF_2'(A_5969, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5970))='#skF_6' | ~v1_partfun1('#skF_6', A_21) | ~v1_partfun1('#skF_2'(A_5969, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5970)), A_21) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_2'(A_5969, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5970)), k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1('#skF_2'(A_5969, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5970))) | ~m1_subset_1(C_5970, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_5970) | '#skF_1'(A_5969, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5970))=A_5969 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5970)=k1_tarski(A_5969))), inference(resolution, [status(thm)], [c_4711, c_34])).
% 7.95/2.71  tff(c_4792, plain, (![A_6035, C_6036, A_6037, B_6038]: ('#skF_2'(A_6035, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6036))='#skF_6' | ~v1_partfun1('#skF_6', A_6037) | ~v1_partfun1('#skF_2'(A_6035, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6036)), A_6037) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_6037, B_6038))) | ~m1_subset_1('#skF_2'(A_6035, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6036)), k1_zfmisc_1(k2_zfmisc_1(A_6037, B_6038))) | ~v1_funct_1('#skF_2'(A_6035, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6036))) | ~m1_subset_1(C_6036, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_6036) | '#skF_1'(A_6035, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6036))=A_6035 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6036)=k1_tarski(A_6035))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4713])).
% 7.95/2.71  tff(c_4796, plain, (![A_1, C_5923]: ('#skF_2'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5923))='#skF_6' | ~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_2'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5923)), '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1('#skF_2'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5923))) | ~m1_subset_1(C_5923, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_5923) | '#skF_1'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5923))=A_1 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_5923)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_4482, c_4792])).
% 7.95/2.71  tff(c_4808, plain, (![A_6039, C_6040]: ('#skF_2'(A_6039, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6040))='#skF_6' | ~v1_partfun1('#skF_2'(A_6039, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6040)), '#skF_3') | ~v1_funct_1('#skF_2'(A_6039, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6040))) | ~m1_subset_1(C_6040, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_6040) | '#skF_1'(A_6039, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6040))=A_6039 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6040)=k1_tarski(A_6039))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_199, c_4796])).
% 7.95/2.71  tff(c_4812, plain, (![A_1, C_75]: ('#skF_2'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_75))='#skF_6' | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_1('#skF_2'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_75))) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_75) | '#skF_1'(A_1, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_75))=A_1 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_75)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_4782, c_4808])).
% 7.95/2.71  tff(c_4816, plain, (![A_6041, C_6042]: ('#skF_2'(A_6041, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6042))='#skF_6' | ~v1_funct_1('#skF_2'(A_6041, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6042))) | ~m1_subset_1(C_6042, k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1(C_6042) | '#skF_1'(A_6041, k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6042))=A_6041 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), C_6042)=k1_tarski(A_6041))), inference(negUnitSimplification, [status(thm)], [c_4473, c_4812])).
% 7.95/2.71  tff(c_4821, plain, (![A_5945]: ('#skF_2'(A_5945, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1('#skF_6') | '#skF_1'(A_5945, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))=A_5945 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski(A_5945))), inference(resolution, [status(thm)], [c_4632, c_4816])).
% 7.95/2.71  tff(c_4825, plain, (![A_5945]: ('#skF_2'(A_5945, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))='#skF_6' | '#skF_1'(A_5945, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))=A_5945 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski(A_5945))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_4821])).
% 7.95/2.71  tff(c_4827, plain, (![A_6043]: ('#skF_2'(A_6043, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))='#skF_6' | '#skF_1'(A_6043, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))=A_6043 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski(A_6043))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_4821])).
% 7.95/2.71  tff(c_4864, plain, (![A_6043]: ('#skF_1'(A_6043, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))=A_6043 | A_6043!='#skF_6' | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski(A_6043) | '#skF_1'(A_6043, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))=A_6043 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski(A_6043))), inference(superposition, [status(thm), theory('equality')], [c_4827, c_8])).
% 7.95/2.71  tff(c_4922, plain, (![A_6045]: (A_6045!='#skF_6' | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski(A_6045) | '#skF_1'(A_6045, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))=A_6045)), inference(factorization, [status(thm), theory('equality')], [c_4864])).
% 7.95/2.71  tff(c_5022, plain, (![A_6056]: (~r2_hidden(A_6056, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')) | '#skF_2'(A_6056, k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))!=A_6056 | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski(A_6056) | A_6056!='#skF_6' | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski(A_6056))), inference(superposition, [status(thm), theory('equality')], [c_4922, c_6])).
% 7.95/2.71  tff(c_5029, plain, ('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))!='#skF_6' | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_4662, c_5022])).
% 7.95/2.71  tff(c_5044, plain, ('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_4609, c_4609, c_5029])).
% 7.95/2.71  tff(c_5049, plain, ('#skF_1'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))='#skF_6' | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4825, c_5044])).
% 7.95/2.71  tff(c_5052, plain, ('#skF_1'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_4609, c_5049])).
% 7.95/2.71  tff(c_5064, plain, (v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1('#skF_6') | ~r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5052, c_152])).
% 7.95/2.71  tff(c_5084, plain, (v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4662, c_52, c_48, c_5064])).
% 7.95/2.71  tff(c_5085, plain, (v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_4609, c_5084])).
% 7.95/2.71  tff(c_5061, plain, (v1_funct_2('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_3', k1_tarski('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1('#skF_6') | ~r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5052, c_207])).
% 7.95/2.71  tff(c_5081, plain, (v1_funct_2('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_3', k1_tarski('#skF_4')) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4662, c_52, c_48, c_5061])).
% 7.95/2.71  tff(c_5082, plain, (v1_funct_2('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_3', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_4609, c_5081])).
% 7.95/2.71  tff(c_4481, plain, (![A_1, A_5921, B_5922, C_5923]: (m1_subset_1('#skF_2'(A_1, k5_partfun1(A_5921, B_5922, C_5923)), k1_zfmisc_1(k2_zfmisc_1(A_5921, B_5922))) | ~m1_subset_1(C_5923, k1_zfmisc_1(k2_zfmisc_1(A_5921, B_5922))) | ~v1_funct_1(C_5923) | ~r2_hidden('#skF_1'(A_1, k5_partfun1(A_5921, B_5922, C_5923)), k5_partfun1(A_5921, B_5922, C_5923)) | k5_partfun1(A_5921, B_5922, C_5923)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_10, c_4474])).
% 7.95/2.71  tff(c_5058, plain, (m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | ~v1_funct_1('#skF_6') | ~r2_hidden('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5052, c_4481])).
% 7.95/2.71  tff(c_5078, plain, (m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))) | k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4662, c_52, c_48, c_5058])).
% 7.95/2.71  tff(c_5079, plain, (m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_4609, c_5078])).
% 7.95/2.71  tff(c_5146, plain, (k1_tarski('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_3') | ~v1_funct_2('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')))), inference(resolution, [status(thm)], [c_5079, c_30])).
% 7.95/2.71  tff(c_5172, plain, (k1_tarski('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5085, c_5082, c_5146])).
% 7.95/2.71  tff(c_5173, plain, (v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_4473, c_5172])).
% 7.95/2.71  tff(c_5141, plain, (r1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_6') | ~v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')))), inference(resolution, [status(thm)], [c_5079, c_4496])).
% 7.95/2.71  tff(c_5166, plain, (r1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5085, c_5141])).
% 7.95/2.71  tff(c_5177, plain, (![A_21, B_22]: ('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))='#skF_6' | ~v1_partfun1('#skF_6', A_21) | ~v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), A_21) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))))), inference(resolution, [status(thm)], [c_5166, c_34])).
% 7.95/2.71  tff(c_5183, plain, (![A_21, B_22]: ('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6'))='#skF_6' | ~v1_partfun1('#skF_6', A_21) | ~v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), A_21) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(demodulation, [status(thm), theory('equality')], [c_5085, c_52, c_5177])).
% 7.95/2.71  tff(c_5187, plain, (![A_6064, B_6065]: (~v1_partfun1('#skF_6', A_6064) | ~v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), A_6064) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_6064, B_6065))) | ~m1_subset_1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(A_6064, B_6065))))), inference(negUnitSimplification, [status(thm)], [c_5044, c_5183])).
% 7.95/2.71  tff(c_5190, plain, (~v1_partfun1('#skF_6', '#skF_3') | ~v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(resolution, [status(thm)], [c_5079, c_5187])).
% 7.95/2.71  tff(c_5210, plain, (~v1_partfun1('#skF_2'('#skF_6', k5_partfun1('#skF_3', k1_tarski('#skF_4'), '#skF_6')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_199, c_5190])).
% 7.95/2.71  tff(c_5229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5173, c_5210])).
% 7.95/2.71  tff(c_5230, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_197])).
% 7.95/2.71  tff(c_5249, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)!=k1_xboole_0 | k1_xboole_0=A_11)), inference(superposition, [status(thm), theory('equality')], [c_5230, c_24])).
% 7.95/2.71  tff(c_5264, plain, (![A_11]: (k1_xboole_0=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5249])).
% 7.95/2.71  tff(c_5234, plain, (k5_partfun1('#skF_3', k1_xboole_0, '#skF_5')!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5230, c_46])).
% 7.95/2.71  tff(c_5814, plain, (k1_tarski('#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5264, c_5234])).
% 7.95/2.71  tff(c_5832, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5264, c_5814])).
% 7.95/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.71  
% 7.95/2.71  Inference rules
% 7.95/2.71  ----------------------
% 7.95/2.71  #Ref     : 0
% 7.95/2.71  #Sup     : 1462
% 7.95/2.71  #Fact    : 14
% 7.95/2.71  #Define  : 0
% 7.95/2.71  #Split   : 14
% 7.95/2.71  #Chain   : 0
% 7.95/2.71  #Close   : 0
% 7.95/2.71  
% 7.95/2.71  Ordering : KBO
% 7.95/2.71  
% 7.95/2.71  Simplification rules
% 7.95/2.71  ----------------------
% 7.95/2.71  #Subsume      : 266
% 7.95/2.71  #Demod        : 1008
% 7.95/2.71  #Tautology    : 283
% 7.95/2.71  #SimpNegUnit  : 128
% 7.95/2.71  #BackRed      : 47
% 7.95/2.71  
% 7.95/2.71  #Partial instantiations: 989
% 7.95/2.71  #Strategies tried      : 1
% 7.95/2.71  
% 7.95/2.71  Timing (in seconds)
% 7.95/2.71  ----------------------
% 7.95/2.71  Preprocessing        : 0.42
% 7.95/2.71  Parsing              : 0.19
% 7.95/2.71  CNF conversion       : 0.04
% 7.95/2.71  Main loop            : 1.44
% 7.95/2.71  Inferencing          : 0.60
% 7.95/2.71  Reduction            : 0.44
% 7.95/2.71  Demodulation         : 0.30
% 7.95/2.71  BG Simplification    : 0.06
% 7.95/2.71  Subsumption          : 0.26
% 7.95/2.71  Abstraction          : 0.09
% 7.95/2.71  MUC search           : 0.00
% 7.95/2.71  Cooper               : 0.00
% 7.95/2.71  Total                : 1.93
% 7.95/2.71  Index Insertion      : 0.00
% 7.95/2.71  Index Deletion       : 0.00
% 7.95/2.71  Index Matching       : 0.00
% 7.95/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
