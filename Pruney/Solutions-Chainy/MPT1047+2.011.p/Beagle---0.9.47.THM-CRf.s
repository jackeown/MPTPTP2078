%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:07 EST 2020

% Result     : Theorem 9.26s
% Output     : CNFRefutation 9.45s
% Verified   : 
% Statistics : Number of formulae       :  218 (24513 expanded)
%              Number of leaves         :   31 (8142 expanded)
%              Depth                    :   28
%              Number of atoms          :  589 (84822 expanded)
%              Number of equality atoms :   97 (17828 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,k1_tarski(B))
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
           => k5_partfun1(A,k1_tarski(B),C) = k1_tarski(D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

tff(f_65,axiom,(
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

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
         => r1_partfun1(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_96,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(c_68,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_62,plain,(
    k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_72,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4073,plain,(
    ! [A_9110,B_9111,C_9112,D_9113] :
      ( '#skF_2'(A_9110,B_9111,C_9112,D_9113) = '#skF_1'(A_9110,B_9111,C_9112,D_9113)
      | r2_hidden('#skF_3'(A_9110,B_9111,C_9112,D_9113),D_9113)
      | k5_partfun1(A_9110,B_9111,C_9112) = D_9113
      | ~ m1_subset_1(C_9112,k1_zfmisc_1(k2_zfmisc_1(A_9110,B_9111)))
      | ~ v1_funct_1(C_9112) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4083,plain,(
    ! [D_9113] :
      ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9113) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9113)
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9113),D_9113)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_9113
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_4073])).

tff(c_4269,plain,(
    ! [D_9129] :
      ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9129) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9129)
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9129),D_9129)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_9129 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4083])).

tff(c_2638,plain,(
    ! [A_9031,B_9032,C_9033,D_9034] :
      ( v1_funct_1('#skF_2'(A_9031,B_9032,C_9033,D_9034))
      | r2_hidden('#skF_3'(A_9031,B_9032,C_9033,D_9034),D_9034)
      | k5_partfun1(A_9031,B_9032,C_9033) = D_9034
      | ~ m1_subset_1(C_9033,k1_zfmisc_1(k2_zfmisc_1(A_9031,B_9032)))
      | ~ v1_funct_1(C_9033) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2640,plain,(
    ! [D_9034] :
      ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9034))
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9034),D_9034)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_9034
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_2638])).

tff(c_2673,plain,(
    ! [D_9036] :
      ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9036))
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9036),D_9036)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_9036 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2640])).

tff(c_139,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_partfun1(C_75,A_76)
      | k5_partfun1(A_76,B_77,C_75) != k1_tarski(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_145,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8') != k1_tarski('#skF_8')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_139])).

tff(c_157,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8') != k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_145])).

tff(c_178,plain,(
    k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8') != k1_tarski('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_159,plain,(
    ! [A_78,B_79,C_80] :
      ( k5_partfun1(A_78,B_79,C_80) = k1_tarski(C_80)
      | ~ v1_partfun1(C_80,A_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_165,plain,
    ( k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_tarski('#skF_8')
    | ~ v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_159])).

tff(c_177,plain,
    ( k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_tarski('#skF_8')
    | ~ v1_partfun1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_165])).

tff(c_180,plain,(
    ~ v1_partfun1('#skF_8','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_177])).

tff(c_185,plain,(
    ! [C_89,D_90,A_91,B_92] :
      ( r1_partfun1(C_89,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_91,k1_tarski(B_92))))
      | ~ v1_funct_1(D_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,k1_tarski(B_92))))
      | ~ v1_funct_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_189,plain,(
    ! [C_89] :
      ( r1_partfun1(C_89,'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_64,c_185])).

tff(c_213,plain,(
    ! [C_94] :
      ( r1_partfun1(C_94,'#skF_8')
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_189])).

tff(c_216,plain,
    ( r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_213])).

tff(c_222,plain,(
    r1_partfun1('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_216])).

tff(c_8,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_610,plain,(
    ! [B_210,D_211,A_212,C_213] :
      ( k1_xboole_0 = B_210
      | r2_hidden(D_211,k5_partfun1(A_212,B_210,C_213))
      | ~ r1_partfun1(C_213,D_211)
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(A_212,B_210)))
      | ~ v1_funct_2(D_211,A_212,B_210)
      | ~ v1_funct_1(D_211)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_212,B_210)))
      | ~ v1_funct_1(C_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_618,plain,(
    ! [C_213] :
      ( k1_tarski('#skF_6') = k1_xboole_0
      | r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_213))
      | ~ r1_partfun1(C_213,'#skF_8')
      | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_213) ) ),
    inference(resolution,[status(thm)],[c_64,c_610])).

tff(c_630,plain,(
    ! [C_213] :
      ( k1_tarski('#skF_6') = k1_xboole_0
      | r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_213))
      | ~ r1_partfun1(C_213,'#skF_8')
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_618])).

tff(c_634,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_630])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k2_zfmisc_1(A_6,k1_tarski(B_7)) != k1_xboole_0
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_665,plain,(
    ! [A_6] :
      ( k2_zfmisc_1(A_6,k1_xboole_0) != k1_xboole_0
      | k1_xboole_0 = A_6 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_12])).

tff(c_672,plain,(
    ! [A_6] : k1_xboole_0 = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_665])).

tff(c_654,plain,(
    k5_partfun1('#skF_5',k1_xboole_0,'#skF_7') != k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_62])).

tff(c_2430,plain,(
    k1_tarski('#skF_8') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_654])).

tff(c_2444,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_2430])).

tff(c_2447,plain,(
    ! [C_8977] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_8977))
      | ~ r1_partfun1(C_8977,'#skF_8')
      | ~ m1_subset_1(C_8977,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_8977) ) ),
    inference(splitRight,[status(thm)],[c_630])).

tff(c_2458,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_2447])).

tff(c_2466,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_222,c_2458])).

tff(c_22,plain,(
    ! [E_46,A_8,B_9,C_10] :
      ( '#skF_4'(E_46,k5_partfun1(A_8,B_9,C_10),A_8,B_9,C_10) = E_46
      | ~ r2_hidden(E_46,k5_partfun1(A_8,B_9,C_10))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2472,plain,
    ( '#skF_4'('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7'),'#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2466,c_22])).

tff(c_2475,plain,(
    '#skF_4'('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7'),'#skF_5',k1_tarski('#skF_6'),'#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2472])).

tff(c_20,plain,(
    ! [E_46,A_8,B_9,C_10] :
      ( v1_partfun1('#skF_4'(E_46,k5_partfun1(A_8,B_9,C_10),A_8,B_9,C_10),A_8)
      | ~ r2_hidden(E_46,k5_partfun1(A_8,B_9,C_10))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2490,plain,
    ( v1_partfun1('#skF_8','#skF_5')
    | ~ r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2475,c_20])).

tff(c_2504,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_2466,c_2490])).

tff(c_2506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_2504])).

tff(c_2508,plain,(
    k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_2566,plain,(
    ! [E_8994,A_8995,B_8996,C_8997] :
      ( '#skF_4'(E_8994,k5_partfun1(A_8995,B_8996,C_8997),A_8995,B_8996,C_8997) = E_8994
      | ~ r2_hidden(E_8994,k5_partfun1(A_8995,B_8996,C_8997))
      | ~ m1_subset_1(C_8997,k1_zfmisc_1(k2_zfmisc_1(A_8995,B_8996)))
      | ~ v1_funct_1(C_8997) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2568,plain,(
    ! [E_8994] :
      ( '#skF_4'(E_8994,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8') = E_8994
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2508,c_2566])).

tff(c_2570,plain,(
    ! [E_8994] :
      ( '#skF_4'(E_8994,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8') = E_8994
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2508,c_2568])).

tff(c_2582,plain,(
    ! [E_9003,A_9004,B_9005,C_9006] :
      ( v1_funct_1('#skF_4'(E_9003,k5_partfun1(A_9004,B_9005,C_9006),A_9004,B_9005,C_9006))
      | ~ r2_hidden(E_9003,k5_partfun1(A_9004,B_9005,C_9006))
      | ~ m1_subset_1(C_9006,k1_zfmisc_1(k2_zfmisc_1(A_9004,B_9005)))
      | ~ v1_funct_1(C_9006) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2586,plain,(
    ! [E_9003] :
      ( v1_funct_1('#skF_4'(E_9003,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ r2_hidden(E_9003,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_2582])).

tff(c_2597,plain,(
    ! [E_9007] :
      ( v1_funct_1('#skF_4'(E_9007,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ r2_hidden(E_9007,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2508,c_2508,c_2586])).

tff(c_2600,plain,(
    ! [E_8994] :
      ( v1_funct_1(E_8994)
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8'))
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2570,c_2597])).

tff(c_2682,plain,
    ( v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_2673,c_2600])).

tff(c_2694,plain,
    ( v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2682])).

tff(c_2771,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2694])).

tff(c_4295,plain,
    ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_4269,c_2771])).

tff(c_4328,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4295])).

tff(c_2649,plain,(
    ! [D_9034] :
      ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9034))
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9034),D_9034)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_9034 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2640])).

tff(c_2777,plain,
    ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_2649,c_2771])).

tff(c_2783,plain,(
    v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2777])).

tff(c_4338,plain,(
    v1_funct_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4328,c_2783])).

tff(c_48,plain,(
    ! [A_8,B_9,C_10,D_32] :
      ( m1_subset_1('#skF_2'(A_8,B_9,C_10,D_32),k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | r2_hidden('#skF_3'(A_8,B_9,C_10,D_32),D_32)
      | k5_partfun1(A_8,B_9,C_10) = D_32
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4342,plain,
    ( m1_subset_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4328,c_48])).

tff(c_4347,plain,
    ( m1_subset_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_4342])).

tff(c_4348,plain,(
    m1_subset_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2771,c_4347])).

tff(c_52,plain,(
    ! [C_52,D_54,A_50,B_51] :
      ( r1_partfun1(C_52,D_54)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_50,k1_tarski(B_51))))
      | ~ v1_funct_1(D_54)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,k1_tarski(B_51))))
      | ~ v1_funct_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4413,plain,(
    ! [C_52] :
      ( r1_partfun1(C_52,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ v1_funct_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_52) ) ),
    inference(resolution,[status(thm)],[c_4348,c_52])).

tff(c_4458,plain,(
    ! [C_52] :
      ( r1_partfun1(C_52,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4338,c_4413])).

tff(c_2696,plain,(
    ! [A_9037,B_9038,C_9039,D_9040] :
      ( ~ r2_hidden('#skF_1'(A_9037,B_9038,C_9039,D_9040),D_9040)
      | r2_hidden('#skF_3'(A_9037,B_9038,C_9039,D_9040),D_9040)
      | k5_partfun1(A_9037,B_9038,C_9039) = D_9040
      | ~ m1_subset_1(C_9039,k1_zfmisc_1(k2_zfmisc_1(A_9037,B_9038)))
      | ~ v1_funct_1(C_9039) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2698,plain,(
    ! [D_9040] :
      ( ~ r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9040),D_9040)
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9040),D_9040)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_9040
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_2696])).

tff(c_2707,plain,(
    ! [D_9040] :
      ( ~ r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9040),D_9040)
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9040),D_9040)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_9040 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2698])).

tff(c_2774,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_2707,c_2771])).

tff(c_2780,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2774])).

tff(c_2818,plain,(
    ! [A_9052,B_9053,C_9054,D_9055] :
      ( v1_partfun1('#skF_2'(A_9052,B_9053,C_9054,D_9055),A_9052)
      | r2_hidden('#skF_3'(A_9052,B_9053,C_9054,D_9055),D_9055)
      | k5_partfun1(A_9052,B_9053,C_9054) = D_9055
      | ~ m1_subset_1(C_9054,k1_zfmisc_1(k2_zfmisc_1(A_9052,B_9053)))
      | ~ v1_funct_1(C_9054) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2820,plain,(
    ! [D_9055] :
      ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9055),'#skF_5')
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9055),D_9055)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_9055
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_2818])).

tff(c_2856,plain,(
    ! [D_9057] :
      ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9057),'#skF_5')
      | r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',D_9057),D_9057)
      | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = D_9057 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2820])).

tff(c_2861,plain,
    ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_2856,c_2771])).

tff(c_2877,plain,(
    v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2861])).

tff(c_4337,plain,(
    v1_partfun1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4328,c_2877])).

tff(c_16,plain,(
    ! [F_49,A_8,B_9,C_10] :
      ( r2_hidden(F_49,k5_partfun1(A_8,B_9,C_10))
      | ~ r1_partfun1(C_10,F_49)
      | ~ v1_partfun1(F_49,A_8)
      | ~ m1_subset_1(F_49,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(F_49)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4393,plain,(
    ! [C_10] :
      ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_10))
      | ~ r1_partfun1(C_10,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ v1_partfun1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
      | ~ v1_funct_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_10) ) ),
    inference(resolution,[status(thm)],[c_4348,c_16])).

tff(c_5573,plain,(
    ! [C_9245] :
      ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_9245))
      | ~ r1_partfun1(C_9245,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_9245,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_9245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4338,c_4337,c_4393])).

tff(c_5581,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2508,c_5573])).

tff(c_5586,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_5581])).

tff(c_5587,plain,(
    ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2780,c_5586])).

tff(c_5591,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4458,c_5587])).

tff(c_5595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_5591])).

tff(c_5597,plain,(
    r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2694])).

tff(c_9190,plain,(
    ! [E_9468,A_9469,B_9470,C_9471] :
      ( m1_subset_1('#skF_4'(E_9468,k5_partfun1(A_9469,B_9470,C_9471),A_9469,B_9470,C_9471),k1_zfmisc_1(k2_zfmisc_1(A_9469,B_9470)))
      | ~ r2_hidden(E_9468,k5_partfun1(A_9469,B_9470,C_9471))
      | ~ m1_subset_1(C_9471,k1_zfmisc_1(k2_zfmisc_1(A_9469,B_9470)))
      | ~ v1_funct_1(C_9471) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9229,plain,(
    ! [E_9468] :
      ( m1_subset_1('#skF_4'(E_9468,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_9468,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2508,c_9190])).

tff(c_9254,plain,(
    ! [E_9472] :
      ( m1_subset_1('#skF_4'(E_9472,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_9472,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2508,c_9229])).

tff(c_9286,plain,(
    ! [E_8994] :
      ( m1_subset_1(E_8994,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8'))
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2570,c_9254])).

tff(c_5603,plain,
    ( v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_5597,c_2600])).

tff(c_5612,plain,(
    v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5597,c_5603])).

tff(c_5808,plain,(
    ! [E_9275,A_9276,B_9277,C_9278] :
      ( m1_subset_1('#skF_4'(E_9275,k5_partfun1(A_9276,B_9277,C_9278),A_9276,B_9277,C_9278),k1_zfmisc_1(k2_zfmisc_1(A_9276,B_9277)))
      | ~ r2_hidden(E_9275,k5_partfun1(A_9276,B_9277,C_9278))
      | ~ m1_subset_1(C_9278,k1_zfmisc_1(k2_zfmisc_1(A_9276,B_9277)))
      | ~ v1_funct_1(C_9278) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5838,plain,(
    ! [E_9275] :
      ( m1_subset_1('#skF_4'(E_9275,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_9275,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2508,c_5808])).

tff(c_5859,plain,(
    ! [E_9279] :
      ( m1_subset_1('#skF_4'(E_9279,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_9279,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2508,c_5838])).

tff(c_5886,plain,(
    ! [E_8994] :
      ( m1_subset_1(E_8994,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8'))
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2570,c_5859])).

tff(c_2621,plain,(
    ! [E_9025,A_9026,B_9027,C_9028] :
      ( v1_partfun1('#skF_4'(E_9025,k5_partfun1(A_9026,B_9027,C_9028),A_9026,B_9027,C_9028),A_9026)
      | ~ r2_hidden(E_9025,k5_partfun1(A_9026,B_9027,C_9028))
      | ~ m1_subset_1(C_9028,k1_zfmisc_1(k2_zfmisc_1(A_9026,B_9027)))
      | ~ v1_funct_1(C_9028) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2626,plain,(
    ! [E_9025] :
      ( v1_partfun1('#skF_4'(E_9025,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'),'#skF_5')
      | ~ r2_hidden(E_9025,k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_8'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2508,c_2621])).

tff(c_2630,plain,(
    ! [E_9029] :
      ( v1_partfun1('#skF_4'(E_9029,k1_tarski('#skF_8'),'#skF_5',k1_tarski('#skF_6'),'#skF_8'),'#skF_5')
      | ~ r2_hidden(E_9029,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_2508,c_2626])).

tff(c_2635,plain,(
    ! [E_8994] :
      ( v1_partfun1(E_8994,'#skF_5')
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8'))
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2570,c_2630])).

tff(c_5599,plain,
    ( v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_5597,c_2635])).

tff(c_5606,plain,(
    v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5597,c_5599])).

tff(c_5897,plain,(
    ! [E_9280] :
      ( m1_subset_1(E_9280,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_9280,k1_tarski('#skF_8'))
      | ~ r2_hidden(E_9280,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2570,c_5859])).

tff(c_6214,plain,(
    ! [C_9288,E_9289] :
      ( r1_partfun1(C_9288,E_9289)
      | ~ v1_funct_1(E_9289)
      | ~ m1_subset_1(C_9288,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_9288)
      | ~ r2_hidden(E_9289,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_5897,c_52])).

tff(c_6223,plain,(
    ! [E_9289] :
      ( r1_partfun1('#skF_7',E_9289)
      | ~ v1_funct_1(E_9289)
      | ~ v1_funct_1('#skF_7')
      | ~ r2_hidden(E_9289,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_70,c_6214])).

tff(c_6235,plain,(
    ! [E_9290] :
      ( r1_partfun1('#skF_7',E_9290)
      | ~ v1_funct_1(E_9290)
      | ~ r2_hidden(E_9290,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6223])).

tff(c_6270,plain,
    ( r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_5597,c_6235])).

tff(c_6306,plain,(
    r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5612,c_6270])).

tff(c_7507,plain,(
    ! [A_9358,B_9359,C_9360,D_9361] :
      ( v1_partfun1('#skF_2'(A_9358,B_9359,C_9360,D_9361),A_9358)
      | ~ r1_partfun1(C_9360,'#skF_3'(A_9358,B_9359,C_9360,D_9361))
      | ~ v1_partfun1('#skF_3'(A_9358,B_9359,C_9360,D_9361),A_9358)
      | ~ m1_subset_1('#skF_3'(A_9358,B_9359,C_9360,D_9361),k1_zfmisc_1(k2_zfmisc_1(A_9358,B_9359)))
      | ~ v1_funct_1('#skF_3'(A_9358,B_9359,C_9360,D_9361))
      | k5_partfun1(A_9358,B_9359,C_9360) = D_9361
      | ~ m1_subset_1(C_9360,k1_zfmisc_1(k2_zfmisc_1(A_9358,B_9359)))
      | ~ v1_funct_1(C_9360) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7512,plain,
    ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6306,c_7507])).

tff(c_7519,plain,
    ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_5612,c_5606,c_7512])).

tff(c_7520,plain,
    ( v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_7519])).

tff(c_7521,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_7520])).

tff(c_7524,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_5886,c_7521])).

tff(c_7528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5597,c_7524])).

tff(c_7530,plain,(
    m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_7520])).

tff(c_8733,plain,(
    ! [A_9417,B_9418,C_9419,D_9420] :
      ( '#skF_2'(A_9417,B_9418,C_9419,D_9420) = '#skF_1'(A_9417,B_9418,C_9419,D_9420)
      | ~ r1_partfun1(C_9419,'#skF_3'(A_9417,B_9418,C_9419,D_9420))
      | ~ v1_partfun1('#skF_3'(A_9417,B_9418,C_9419,D_9420),A_9417)
      | ~ m1_subset_1('#skF_3'(A_9417,B_9418,C_9419,D_9420),k1_zfmisc_1(k2_zfmisc_1(A_9417,B_9418)))
      | ~ v1_funct_1('#skF_3'(A_9417,B_9418,C_9419,D_9420))
      | k5_partfun1(A_9417,B_9418,C_9419) = D_9420
      | ~ m1_subset_1(C_9419,k1_zfmisc_1(k2_zfmisc_1(A_9417,B_9418)))
      | ~ v1_funct_1(C_9419) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8747,plain,
    ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6306,c_8733])).

tff(c_8764,plain,
    ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_5612,c_7530,c_5606,c_8747])).

tff(c_8765,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8764])).

tff(c_8409,plain,(
    ! [A_9404,B_9405,C_9406,D_9407] :
      ( '#skF_2'(A_9404,B_9405,C_9406,D_9407) = '#skF_1'(A_9404,B_9405,C_9406,D_9407)
      | ~ r1_partfun1(C_9406,'#skF_3'(A_9404,B_9405,C_9406,D_9407))
      | ~ v1_partfun1('#skF_3'(A_9404,B_9405,C_9406,D_9407),A_9404)
      | ~ m1_subset_1('#skF_3'(A_9404,B_9405,C_9406,D_9407),k1_zfmisc_1(k2_zfmisc_1(A_9404,B_9405)))
      | ~ v1_funct_1('#skF_3'(A_9404,B_9405,C_9406,D_9407))
      | k5_partfun1(A_9404,B_9405,C_9406) = D_9407
      | ~ m1_subset_1(C_9406,k1_zfmisc_1(k2_zfmisc_1(A_9404,B_9405)))
      | ~ v1_funct_1(C_9406) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8423,plain,
    ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6306,c_8409])).

tff(c_8440,plain,
    ( '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_5612,c_7530,c_5606,c_8423])).

tff(c_8441,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) = '#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8440])).

tff(c_2676,plain,
    ( v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_2673,c_2635])).

tff(c_2688,plain,
    ( v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2676])).

tff(c_5614,plain,
    ( v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5597,c_2688])).

tff(c_5615,plain,(
    v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_5614])).

tff(c_8451,plain,(
    v1_funct_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8441,c_5615])).

tff(c_8231,plain,(
    ! [A_9398,B_9399,C_9400,D_9401] :
      ( m1_subset_1('#skF_2'(A_9398,B_9399,C_9400,D_9401),k1_zfmisc_1(k2_zfmisc_1(A_9398,B_9399)))
      | ~ r1_partfun1(C_9400,'#skF_3'(A_9398,B_9399,C_9400,D_9401))
      | ~ v1_partfun1('#skF_3'(A_9398,B_9399,C_9400,D_9401),A_9398)
      | ~ m1_subset_1('#skF_3'(A_9398,B_9399,C_9400,D_9401),k1_zfmisc_1(k2_zfmisc_1(A_9398,B_9399)))
      | ~ v1_funct_1('#skF_3'(A_9398,B_9399,C_9400,D_9401))
      | k5_partfun1(A_9398,B_9399,C_9400) = D_9401
      | ~ m1_subset_1(C_9400,k1_zfmisc_1(k2_zfmisc_1(A_9398,B_9399)))
      | ~ v1_funct_1(C_9400) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8242,plain,
    ( m1_subset_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6306,c_8231])).

tff(c_8256,plain,
    ( m1_subset_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_5612,c_7530,c_5606,c_8242])).

tff(c_8257,plain,(
    m1_subset_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8256])).

tff(c_8448,plain,(
    m1_subset_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8441,c_8257])).

tff(c_8514,plain,(
    ! [C_52] :
      ( r1_partfun1(C_52,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ v1_funct_1('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_52) ) ),
    inference(resolution,[status(thm)],[c_8448,c_52])).

tff(c_8562,plain,(
    ! [C_52] :
      ( r1_partfun1(C_52,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8451,c_8514])).

tff(c_2523,plain,(
    ! [C_8984,D_8985,A_8986,B_8987] :
      ( r1_partfun1(C_8984,D_8985)
      | ~ m1_subset_1(D_8985,k1_zfmisc_1(k2_zfmisc_1(A_8986,k1_tarski(B_8987))))
      | ~ v1_funct_1(D_8985)
      | ~ m1_subset_1(C_8984,k1_zfmisc_1(k2_zfmisc_1(A_8986,k1_tarski(B_8987))))
      | ~ v1_funct_1(C_8984) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2527,plain,(
    ! [C_8984] :
      ( r1_partfun1(C_8984,'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_8984,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_8984) ) ),
    inference(resolution,[status(thm)],[c_64,c_2523])).

tff(c_2536,plain,(
    ! [C_8984] :
      ( r1_partfun1(C_8984,'#skF_8')
      | ~ m1_subset_1(C_8984,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_8984) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2527])).

tff(c_8283,plain,
    ( r1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_8')
    | ~ v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_8257,c_2536])).

tff(c_8330,plain,(
    r1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5615,c_8283])).

tff(c_7529,plain,(
    v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_7520])).

tff(c_60,plain,(
    ! [A_60,B_61,C_62] :
      ( k5_partfun1(A_60,B_61,C_62) = k1_tarski(C_62)
      | ~ v1_partfun1(C_62,A_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8291,plain,
    ( k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) = k1_tarski('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_8257,c_60])).

tff(c_8339,plain,(
    k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) = k1_tarski('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5615,c_7529,c_8291])).

tff(c_2507,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_6188,plain,(
    ! [F_9284,A_9285,B_9286,C_9287] :
      ( r2_hidden(F_9284,k5_partfun1(A_9285,B_9286,C_9287))
      | ~ r1_partfun1(C_9287,F_9284)
      | ~ v1_partfun1(F_9284,A_9285)
      | ~ m1_subset_1(F_9284,k1_zfmisc_1(k2_zfmisc_1(A_9285,B_9286)))
      | ~ v1_funct_1(F_9284)
      | ~ m1_subset_1(C_9287,k1_zfmisc_1(k2_zfmisc_1(A_9285,B_9286)))
      | ~ v1_funct_1(C_9287) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6198,plain,(
    ! [C_9287] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_9287))
      | ~ r1_partfun1(C_9287,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_9287,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_9287) ) ),
    inference(resolution,[status(thm)],[c_64,c_6188])).

tff(c_6478,plain,(
    ! [C_9295] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_9295))
      | ~ r1_partfun1(C_9295,'#skF_8')
      | ~ m1_subset_1(C_9295,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_9295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2507,c_6198])).

tff(c_6495,plain,(
    ! [E_8994] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5',k1_tarski('#skF_6'),E_8994))
      | ~ r1_partfun1(E_8994,'#skF_8')
      | ~ v1_funct_1(E_8994)
      | ~ r2_hidden(E_8994,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_5886,c_6478])).

tff(c_8377,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))))
    | ~ r1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_8')
    | ~ v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8339,c_6495])).

tff(c_8398,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))))
    | ~ r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5615,c_8330,c_8377])).

tff(c_8408,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_8398])).

tff(c_8442,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8441,c_8408])).

tff(c_8270,plain,(
    ! [C_10] :
      ( r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_10))
      | ~ r1_partfun1(C_10,'#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ v1_partfun1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
      | ~ v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_10) ) ),
    inference(resolution,[status(thm)],[c_8257,c_16])).

tff(c_8312,plain,(
    ! [C_10] :
      ( r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_10))
      | ~ r1_partfun1(C_10,'#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5615,c_7529,c_8270])).

tff(c_8655,plain,(
    ! [C_9416] :
      ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k5_partfun1('#skF_5',k1_tarski('#skF_6'),C_9416))
      | ~ r1_partfun1(C_9416,'#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
      | ~ m1_subset_1(C_9416,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_9416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8441,c_8441,c_8312])).

tff(c_8666,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2508,c_8655])).

tff(c_8673,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_8666])).

tff(c_8674,plain,(
    ~ r1_partfun1('#skF_8','#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_8442,c_8673])).

tff(c_8677,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8562,c_8674])).

tff(c_8681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_8677])).

tff(c_8683,plain,(
    r2_hidden('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_8398])).

tff(c_8767,plain,(
    r2_hidden('#skF_1'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8765,c_8683])).

tff(c_28,plain,(
    ! [A_8,B_9,C_10,D_32] :
      ( ~ r2_hidden('#skF_1'(A_8,B_9,C_10,D_32),D_32)
      | ~ r1_partfun1(C_10,'#skF_3'(A_8,B_9,C_10,D_32))
      | ~ v1_partfun1('#skF_3'(A_8,B_9,C_10,D_32),A_8)
      | ~ m1_subset_1('#skF_3'(A_8,B_9,C_10,D_32),k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1('#skF_3'(A_8,B_9,C_10,D_32))
      | k5_partfun1(A_8,B_9,C_10) = D_32
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8811,plain,
    ( ~ r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_8767,c_28])).

tff(c_8837,plain,(
    k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_5612,c_7530,c_5606,c_6306,c_8811])).

tff(c_8839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8837])).

tff(c_8841,plain,(
    ~ v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_5614])).

tff(c_8840,plain,(
    v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5614])).

tff(c_9299,plain,(
    ! [E_9473] :
      ( m1_subset_1(E_9473,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ r2_hidden(E_9473,k1_tarski('#skF_8'))
      | ~ r2_hidden(E_9473,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2570,c_9254])).

tff(c_9746,plain,(
    ! [C_9482,E_9483] :
      ( r1_partfun1(C_9482,E_9483)
      | ~ v1_funct_1(E_9483)
      | ~ m1_subset_1(C_9482,k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
      | ~ v1_funct_1(C_9482)
      | ~ r2_hidden(E_9483,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_9299,c_52])).

tff(c_9758,plain,(
    ! [E_9483] :
      ( r1_partfun1('#skF_7',E_9483)
      | ~ v1_funct_1(E_9483)
      | ~ v1_funct_1('#skF_7')
      | ~ r2_hidden(E_9483,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_70,c_9746])).

tff(c_9771,plain,(
    ! [E_9484] :
      ( r1_partfun1('#skF_7',E_9484)
      | ~ v1_funct_1(E_9484)
      | ~ r2_hidden(E_9484,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9758])).

tff(c_9839,plain,
    ( r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(resolution,[status(thm)],[c_2649,c_9771])).

tff(c_9878,plain,
    ( r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5612,c_9839])).

tff(c_9879,plain,(
    r1_partfun1('#skF_7','#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8841,c_9878])).

tff(c_10364,plain,(
    ! [A_9502,B_9503,C_9504,D_9505] :
      ( v1_funct_1('#skF_2'(A_9502,B_9503,C_9504,D_9505))
      | ~ r1_partfun1(C_9504,'#skF_3'(A_9502,B_9503,C_9504,D_9505))
      | ~ v1_partfun1('#skF_3'(A_9502,B_9503,C_9504,D_9505),A_9502)
      | ~ m1_subset_1('#skF_3'(A_9502,B_9503,C_9504,D_9505),k1_zfmisc_1(k2_zfmisc_1(A_9502,B_9503)))
      | ~ v1_funct_1('#skF_3'(A_9502,B_9503,C_9504,D_9505))
      | k5_partfun1(A_9502,B_9503,C_9504) = D_9505
      | ~ m1_subset_1(C_9504,k1_zfmisc_1(k2_zfmisc_1(A_9502,B_9503)))
      | ~ v1_funct_1(C_9504) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10369,plain,
    ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ v1_partfun1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_9879,c_10364])).

tff(c_10376,plain,
    ( v1_funct_1('#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')))
    | ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))))
    | k5_partfun1('#skF_5',k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_5612,c_8840,c_10369])).

tff(c_10377,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8841,c_10376])).

tff(c_10380,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k1_tarski('#skF_6'),'#skF_7',k1_tarski('#skF_8')),k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_9286,c_10377])).

tff(c_10384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5597,c_10380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.26/3.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.45/3.08  
% 9.45/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.45/3.08  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 9.45/3.08  
% 9.45/3.08  %Foreground sorts:
% 9.45/3.08  
% 9.45/3.08  
% 9.45/3.08  %Background operators:
% 9.45/3.08  
% 9.45/3.08  
% 9.45/3.08  %Foreground operators:
% 9.45/3.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.45/3.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.45/3.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.45/3.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.45/3.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.45/3.08  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 9.45/3.08  tff('#skF_7', type, '#skF_7': $i).
% 9.45/3.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.45/3.08  tff('#skF_5', type, '#skF_5': $i).
% 9.45/3.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.45/3.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.45/3.08  tff('#skF_6', type, '#skF_6': $i).
% 9.45/3.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.45/3.08  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.45/3.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.45/3.08  tff('#skF_8', type, '#skF_8': $i).
% 9.45/3.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.45/3.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.45/3.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.45/3.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.45/3.08  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.45/3.08  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 9.45/3.08  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 9.45/3.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.45/3.08  
% 9.45/3.12  tff(f_118, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (k5_partfun1(A, k1_tarski(B), C) = k1_tarski(D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_2)).
% 9.45/3.12  tff(f_65, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 9.45/3.12  tff(f_104, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_partfun1)).
% 9.45/3.12  tff(f_76, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => r1_partfun1(C, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_partfun1)).
% 9.45/3.12  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.45/3.12  tff(f_96, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 9.45/3.12  tff(f_44, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 9.45/3.12  tff(c_68, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.45/3.12  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.45/3.12  tff(c_62, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.45/3.12  tff(c_72, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.45/3.12  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.45/3.12  tff(c_4073, plain, (![A_9110, B_9111, C_9112, D_9113]: ('#skF_2'(A_9110, B_9111, C_9112, D_9113)='#skF_1'(A_9110, B_9111, C_9112, D_9113) | r2_hidden('#skF_3'(A_9110, B_9111, C_9112, D_9113), D_9113) | k5_partfun1(A_9110, B_9111, C_9112)=D_9113 | ~m1_subset_1(C_9112, k1_zfmisc_1(k2_zfmisc_1(A_9110, B_9111))) | ~v1_funct_1(C_9112))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_4083, plain, (![D_9113]: ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9113)='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9113) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9113), D_9113) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_9113 | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_4073])).
% 9.45/3.12  tff(c_4269, plain, (![D_9129]: ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9129)='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9129) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9129), D_9129) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_9129)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4083])).
% 9.45/3.12  tff(c_2638, plain, (![A_9031, B_9032, C_9033, D_9034]: (v1_funct_1('#skF_2'(A_9031, B_9032, C_9033, D_9034)) | r2_hidden('#skF_3'(A_9031, B_9032, C_9033, D_9034), D_9034) | k5_partfun1(A_9031, B_9032, C_9033)=D_9034 | ~m1_subset_1(C_9033, k1_zfmisc_1(k2_zfmisc_1(A_9031, B_9032))) | ~v1_funct_1(C_9033))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_2640, plain, (![D_9034]: (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9034)) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9034), D_9034) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_9034 | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_2638])).
% 9.45/3.12  tff(c_2673, plain, (![D_9036]: (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9036)) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9036), D_9036) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_9036)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2640])).
% 9.45/3.12  tff(c_139, plain, (![C_75, A_76, B_77]: (v1_partfun1(C_75, A_76) | k5_partfun1(A_76, B_77, C_75)!=k1_tarski(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_1(C_75))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.45/3.12  tff(c_145, plain, (v1_partfun1('#skF_8', '#skF_5') | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')!=k1_tarski('#skF_8') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_139])).
% 9.45/3.12  tff(c_157, plain, (v1_partfun1('#skF_8', '#skF_5') | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')!=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_145])).
% 9.45/3.12  tff(c_178, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')!=k1_tarski('#skF_8')), inference(splitLeft, [status(thm)], [c_157])).
% 9.45/3.12  tff(c_159, plain, (![A_78, B_79, C_80]: (k5_partfun1(A_78, B_79, C_80)=k1_tarski(C_80) | ~v1_partfun1(C_80, A_78) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.45/3.12  tff(c_165, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_tarski('#skF_8') | ~v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_159])).
% 9.45/3.12  tff(c_177, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_tarski('#skF_8') | ~v1_partfun1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_165])).
% 9.45/3.12  tff(c_180, plain, (~v1_partfun1('#skF_8', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_178, c_177])).
% 9.45/3.12  tff(c_185, plain, (![C_89, D_90, A_91, B_92]: (r1_partfun1(C_89, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_91, k1_tarski(B_92)))) | ~v1_funct_1(D_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, k1_tarski(B_92)))) | ~v1_funct_1(C_89))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.45/3.12  tff(c_189, plain, (![C_89]: (r1_partfun1(C_89, '#skF_8') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_89))), inference(resolution, [status(thm)], [c_64, c_185])).
% 9.45/3.12  tff(c_213, plain, (![C_94]: (r1_partfun1(C_94, '#skF_8') | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_94))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_189])).
% 9.45/3.12  tff(c_216, plain, (r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_213])).
% 9.45/3.12  tff(c_222, plain, (r1_partfun1('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_216])).
% 9.45/3.12  tff(c_8, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.45/3.12  tff(c_66, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.45/3.12  tff(c_610, plain, (![B_210, D_211, A_212, C_213]: (k1_xboole_0=B_210 | r2_hidden(D_211, k5_partfun1(A_212, B_210, C_213)) | ~r1_partfun1(C_213, D_211) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(A_212, B_210))) | ~v1_funct_2(D_211, A_212, B_210) | ~v1_funct_1(D_211) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_212, B_210))) | ~v1_funct_1(C_213))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.45/3.12  tff(c_618, plain, (![C_213]: (k1_tarski('#skF_6')=k1_xboole_0 | r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_213)) | ~r1_partfun1(C_213, '#skF_8') | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_213))), inference(resolution, [status(thm)], [c_64, c_610])).
% 9.45/3.12  tff(c_630, plain, (![C_213]: (k1_tarski('#skF_6')=k1_xboole_0 | r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_213)) | ~r1_partfun1(C_213, '#skF_8') | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_213))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_618])).
% 9.45/3.12  tff(c_634, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_630])).
% 9.45/3.12  tff(c_12, plain, (![A_6, B_7]: (k2_zfmisc_1(A_6, k1_tarski(B_7))!=k1_xboole_0 | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.45/3.12  tff(c_665, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)!=k1_xboole_0 | k1_xboole_0=A_6)), inference(superposition, [status(thm), theory('equality')], [c_634, c_12])).
% 9.45/3.12  tff(c_672, plain, (![A_6]: (k1_xboole_0=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_665])).
% 9.45/3.12  tff(c_654, plain, (k5_partfun1('#skF_5', k1_xboole_0, '#skF_7')!=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_634, c_62])).
% 9.45/3.12  tff(c_2430, plain, (k1_tarski('#skF_8')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_672, c_654])).
% 9.45/3.12  tff(c_2444, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_672, c_2430])).
% 9.45/3.12  tff(c_2447, plain, (![C_8977]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_8977)) | ~r1_partfun1(C_8977, '#skF_8') | ~m1_subset_1(C_8977, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_8977))), inference(splitRight, [status(thm)], [c_630])).
% 9.45/3.12  tff(c_2458, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_2447])).
% 9.45/3.12  tff(c_2466, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_222, c_2458])).
% 9.45/3.12  tff(c_22, plain, (![E_46, A_8, B_9, C_10]: ('#skF_4'(E_46, k5_partfun1(A_8, B_9, C_10), A_8, B_9, C_10)=E_46 | ~r2_hidden(E_46, k5_partfun1(A_8, B_9, C_10)) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_2472, plain, ('#skF_4'('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7'), '#skF_5', k1_tarski('#skF_6'), '#skF_7')='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_2466, c_22])).
% 9.45/3.12  tff(c_2475, plain, ('#skF_4'('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7'), '#skF_5', k1_tarski('#skF_6'), '#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2472])).
% 9.45/3.12  tff(c_20, plain, (![E_46, A_8, B_9, C_10]: (v1_partfun1('#skF_4'(E_46, k5_partfun1(A_8, B_9, C_10), A_8, B_9, C_10), A_8) | ~r2_hidden(E_46, k5_partfun1(A_8, B_9, C_10)) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_2490, plain, (v1_partfun1('#skF_8', '#skF_5') | ~r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2475, c_20])).
% 9.45/3.12  tff(c_2504, plain, (v1_partfun1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_2466, c_2490])).
% 9.45/3.12  tff(c_2506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_2504])).
% 9.45/3.12  tff(c_2508, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_157])).
% 9.45/3.12  tff(c_2566, plain, (![E_8994, A_8995, B_8996, C_8997]: ('#skF_4'(E_8994, k5_partfun1(A_8995, B_8996, C_8997), A_8995, B_8996, C_8997)=E_8994 | ~r2_hidden(E_8994, k5_partfun1(A_8995, B_8996, C_8997)) | ~m1_subset_1(C_8997, k1_zfmisc_1(k2_zfmisc_1(A_8995, B_8996))) | ~v1_funct_1(C_8997))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_2568, plain, (![E_8994]: ('#skF_4'(E_8994, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8')=E_8994 | ~r2_hidden(E_8994, k1_tarski('#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2508, c_2566])).
% 9.45/3.12  tff(c_2570, plain, (![E_8994]: ('#skF_4'(E_8994, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8')=E_8994 | ~r2_hidden(E_8994, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2508, c_2568])).
% 9.45/3.12  tff(c_2582, plain, (![E_9003, A_9004, B_9005, C_9006]: (v1_funct_1('#skF_4'(E_9003, k5_partfun1(A_9004, B_9005, C_9006), A_9004, B_9005, C_9006)) | ~r2_hidden(E_9003, k5_partfun1(A_9004, B_9005, C_9006)) | ~m1_subset_1(C_9006, k1_zfmisc_1(k2_zfmisc_1(A_9004, B_9005))) | ~v1_funct_1(C_9006))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_2586, plain, (![E_9003]: (v1_funct_1('#skF_4'(E_9003, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~r2_hidden(E_9003, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~v1_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_2582])).
% 9.45/3.12  tff(c_2597, plain, (![E_9007]: (v1_funct_1('#skF_4'(E_9007, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~r2_hidden(E_9007, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2508, c_2508, c_2586])).
% 9.45/3.12  tff(c_2600, plain, (![E_8994]: (v1_funct_1(E_8994) | ~r2_hidden(E_8994, k1_tarski('#skF_8')) | ~r2_hidden(E_8994, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2570, c_2597])).
% 9.45/3.12  tff(c_2682, plain, (v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_2673, c_2600])).
% 9.45/3.12  tff(c_2694, plain, (v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_62, c_2682])).
% 9.45/3.12  tff(c_2771, plain, (~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_2694])).
% 9.45/3.12  tff(c_4295, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_4269, c_2771])).
% 9.45/3.12  tff(c_4328, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_62, c_4295])).
% 9.45/3.12  tff(c_2649, plain, (![D_9034]: (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9034)) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9034), D_9034) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_9034)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2640])).
% 9.45/3.12  tff(c_2777, plain, (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_2649, c_2771])).
% 9.45/3.12  tff(c_2783, plain, (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_62, c_2777])).
% 9.45/3.12  tff(c_4338, plain, (v1_funct_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_4328, c_2783])).
% 9.45/3.12  tff(c_48, plain, (![A_8, B_9, C_10, D_32]: (m1_subset_1('#skF_2'(A_8, B_9, C_10, D_32), k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | r2_hidden('#skF_3'(A_8, B_9, C_10, D_32), D_32) | k5_partfun1(A_8, B_9, C_10)=D_32 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_4342, plain, (m1_subset_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4328, c_48])).
% 9.45/3.12  tff(c_4347, plain, (m1_subset_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_4342])).
% 9.45/3.12  tff(c_4348, plain, (m1_subset_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_2771, c_4347])).
% 9.45/3.12  tff(c_52, plain, (![C_52, D_54, A_50, B_51]: (r1_partfun1(C_52, D_54) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_50, k1_tarski(B_51)))) | ~v1_funct_1(D_54) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, k1_tarski(B_51)))) | ~v1_funct_1(C_52))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.45/3.12  tff(c_4413, plain, (![C_52]: (r1_partfun1(C_52, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_funct_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_52))), inference(resolution, [status(thm)], [c_4348, c_52])).
% 9.45/3.12  tff(c_4458, plain, (![C_52]: (r1_partfun1(C_52, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_52))), inference(demodulation, [status(thm), theory('equality')], [c_4338, c_4413])).
% 9.45/3.12  tff(c_2696, plain, (![A_9037, B_9038, C_9039, D_9040]: (~r2_hidden('#skF_1'(A_9037, B_9038, C_9039, D_9040), D_9040) | r2_hidden('#skF_3'(A_9037, B_9038, C_9039, D_9040), D_9040) | k5_partfun1(A_9037, B_9038, C_9039)=D_9040 | ~m1_subset_1(C_9039, k1_zfmisc_1(k2_zfmisc_1(A_9037, B_9038))) | ~v1_funct_1(C_9039))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_2698, plain, (![D_9040]: (~r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9040), D_9040) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9040), D_9040) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_9040 | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_2696])).
% 9.45/3.12  tff(c_2707, plain, (![D_9040]: (~r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9040), D_9040) | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9040), D_9040) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_9040)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2698])).
% 9.45/3.12  tff(c_2774, plain, (~r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_2707, c_2771])).
% 9.45/3.12  tff(c_2780, plain, (~r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_62, c_2774])).
% 9.45/3.12  tff(c_2818, plain, (![A_9052, B_9053, C_9054, D_9055]: (v1_partfun1('#skF_2'(A_9052, B_9053, C_9054, D_9055), A_9052) | r2_hidden('#skF_3'(A_9052, B_9053, C_9054, D_9055), D_9055) | k5_partfun1(A_9052, B_9053, C_9054)=D_9055 | ~m1_subset_1(C_9054, k1_zfmisc_1(k2_zfmisc_1(A_9052, B_9053))) | ~v1_funct_1(C_9054))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_2820, plain, (![D_9055]: (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9055), '#skF_5') | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9055), D_9055) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_9055 | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_2818])).
% 9.45/3.12  tff(c_2856, plain, (![D_9057]: (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9057), '#skF_5') | r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', D_9057), D_9057) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=D_9057)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2820])).
% 9.45/3.12  tff(c_2861, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_2856, c_2771])).
% 9.45/3.12  tff(c_2877, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_2861])).
% 9.45/3.12  tff(c_4337, plain, (v1_partfun1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4328, c_2877])).
% 9.45/3.12  tff(c_16, plain, (![F_49, A_8, B_9, C_10]: (r2_hidden(F_49, k5_partfun1(A_8, B_9, C_10)) | ~r1_partfun1(C_10, F_49) | ~v1_partfun1(F_49, A_8) | ~m1_subset_1(F_49, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(F_49) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_4393, plain, (![C_10]: (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_10)) | ~r1_partfun1(C_10, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_partfun1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~v1_funct_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_10))), inference(resolution, [status(thm)], [c_4348, c_16])).
% 9.45/3.12  tff(c_5573, plain, (![C_9245]: (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_9245)) | ~r1_partfun1(C_9245, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_9245, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_9245))), inference(demodulation, [status(thm), theory('equality')], [c_4338, c_4337, c_4393])).
% 9.45/3.12  tff(c_5581, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | ~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2508, c_5573])).
% 9.45/3.12  tff(c_5586, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | ~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_5581])).
% 9.45/3.12  tff(c_5587, plain, (~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_2780, c_5586])).
% 9.45/3.12  tff(c_5591, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_4458, c_5587])).
% 9.45/3.12  tff(c_5595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_5591])).
% 9.45/3.12  tff(c_5597, plain, (r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_2694])).
% 9.45/3.12  tff(c_9190, plain, (![E_9468, A_9469, B_9470, C_9471]: (m1_subset_1('#skF_4'(E_9468, k5_partfun1(A_9469, B_9470, C_9471), A_9469, B_9470, C_9471), k1_zfmisc_1(k2_zfmisc_1(A_9469, B_9470))) | ~r2_hidden(E_9468, k5_partfun1(A_9469, B_9470, C_9471)) | ~m1_subset_1(C_9471, k1_zfmisc_1(k2_zfmisc_1(A_9469, B_9470))) | ~v1_funct_1(C_9471))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_9229, plain, (![E_9468]: (m1_subset_1('#skF_4'(E_9468, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_9468, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2508, c_9190])).
% 9.45/3.12  tff(c_9254, plain, (![E_9472]: (m1_subset_1('#skF_4'(E_9472, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_9472, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2508, c_9229])).
% 9.45/3.12  tff(c_9286, plain, (![E_8994]: (m1_subset_1(E_8994, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_8994, k1_tarski('#skF_8')) | ~r2_hidden(E_8994, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2570, c_9254])).
% 9.45/3.12  tff(c_5603, plain, (v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_5597, c_2600])).
% 9.45/3.12  tff(c_5612, plain, (v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_5597, c_5603])).
% 9.45/3.12  tff(c_5808, plain, (![E_9275, A_9276, B_9277, C_9278]: (m1_subset_1('#skF_4'(E_9275, k5_partfun1(A_9276, B_9277, C_9278), A_9276, B_9277, C_9278), k1_zfmisc_1(k2_zfmisc_1(A_9276, B_9277))) | ~r2_hidden(E_9275, k5_partfun1(A_9276, B_9277, C_9278)) | ~m1_subset_1(C_9278, k1_zfmisc_1(k2_zfmisc_1(A_9276, B_9277))) | ~v1_funct_1(C_9278))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_5838, plain, (![E_9275]: (m1_subset_1('#skF_4'(E_9275, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_9275, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2508, c_5808])).
% 9.45/3.12  tff(c_5859, plain, (![E_9279]: (m1_subset_1('#skF_4'(E_9279, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_9279, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2508, c_5838])).
% 9.45/3.12  tff(c_5886, plain, (![E_8994]: (m1_subset_1(E_8994, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_8994, k1_tarski('#skF_8')) | ~r2_hidden(E_8994, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2570, c_5859])).
% 9.45/3.12  tff(c_2621, plain, (![E_9025, A_9026, B_9027, C_9028]: (v1_partfun1('#skF_4'(E_9025, k5_partfun1(A_9026, B_9027, C_9028), A_9026, B_9027, C_9028), A_9026) | ~r2_hidden(E_9025, k5_partfun1(A_9026, B_9027, C_9028)) | ~m1_subset_1(C_9028, k1_zfmisc_1(k2_zfmisc_1(A_9026, B_9027))) | ~v1_funct_1(C_9028))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_2626, plain, (![E_9025]: (v1_partfun1('#skF_4'(E_9025, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8'), '#skF_5') | ~r2_hidden(E_9025, k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2508, c_2621])).
% 9.45/3.12  tff(c_2630, plain, (![E_9029]: (v1_partfun1('#skF_4'(E_9029, k1_tarski('#skF_8'), '#skF_5', k1_tarski('#skF_6'), '#skF_8'), '#skF_5') | ~r2_hidden(E_9029, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_2508, c_2626])).
% 9.45/3.12  tff(c_2635, plain, (![E_8994]: (v1_partfun1(E_8994, '#skF_5') | ~r2_hidden(E_8994, k1_tarski('#skF_8')) | ~r2_hidden(E_8994, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2570, c_2630])).
% 9.45/3.12  tff(c_5599, plain, (v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_5597, c_2635])).
% 9.45/3.12  tff(c_5606, plain, (v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5597, c_5599])).
% 9.45/3.12  tff(c_5897, plain, (![E_9280]: (m1_subset_1(E_9280, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_9280, k1_tarski('#skF_8')) | ~r2_hidden(E_9280, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2570, c_5859])).
% 9.45/3.12  tff(c_6214, plain, (![C_9288, E_9289]: (r1_partfun1(C_9288, E_9289) | ~v1_funct_1(E_9289) | ~m1_subset_1(C_9288, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_9288) | ~r2_hidden(E_9289, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_5897, c_52])).
% 9.45/3.12  tff(c_6223, plain, (![E_9289]: (r1_partfun1('#skF_7', E_9289) | ~v1_funct_1(E_9289) | ~v1_funct_1('#skF_7') | ~r2_hidden(E_9289, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_70, c_6214])).
% 9.45/3.12  tff(c_6235, plain, (![E_9290]: (r1_partfun1('#skF_7', E_9290) | ~v1_funct_1(E_9290) | ~r2_hidden(E_9290, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6223])).
% 9.45/3.12  tff(c_6270, plain, (r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_5597, c_6235])).
% 9.45/3.12  tff(c_6306, plain, (r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_5612, c_6270])).
% 9.45/3.12  tff(c_7507, plain, (![A_9358, B_9359, C_9360, D_9361]: (v1_partfun1('#skF_2'(A_9358, B_9359, C_9360, D_9361), A_9358) | ~r1_partfun1(C_9360, '#skF_3'(A_9358, B_9359, C_9360, D_9361)) | ~v1_partfun1('#skF_3'(A_9358, B_9359, C_9360, D_9361), A_9358) | ~m1_subset_1('#skF_3'(A_9358, B_9359, C_9360, D_9361), k1_zfmisc_1(k2_zfmisc_1(A_9358, B_9359))) | ~v1_funct_1('#skF_3'(A_9358, B_9359, C_9360, D_9361)) | k5_partfun1(A_9358, B_9359, C_9360)=D_9361 | ~m1_subset_1(C_9360, k1_zfmisc_1(k2_zfmisc_1(A_9358, B_9359))) | ~v1_funct_1(C_9360))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_7512, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_6306, c_7507])).
% 9.45/3.12  tff(c_7519, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_5612, c_5606, c_7512])).
% 9.45/3.12  tff(c_7520, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_7519])).
% 9.45/3.12  tff(c_7521, plain, (~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(splitLeft, [status(thm)], [c_7520])).
% 9.45/3.12  tff(c_7524, plain, (~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_5886, c_7521])).
% 9.45/3.12  tff(c_7528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5597, c_7524])).
% 9.45/3.12  tff(c_7530, plain, (m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(splitRight, [status(thm)], [c_7520])).
% 9.45/3.12  tff(c_8733, plain, (![A_9417, B_9418, C_9419, D_9420]: ('#skF_2'(A_9417, B_9418, C_9419, D_9420)='#skF_1'(A_9417, B_9418, C_9419, D_9420) | ~r1_partfun1(C_9419, '#skF_3'(A_9417, B_9418, C_9419, D_9420)) | ~v1_partfun1('#skF_3'(A_9417, B_9418, C_9419, D_9420), A_9417) | ~m1_subset_1('#skF_3'(A_9417, B_9418, C_9419, D_9420), k1_zfmisc_1(k2_zfmisc_1(A_9417, B_9418))) | ~v1_funct_1('#skF_3'(A_9417, B_9418, C_9419, D_9420)) | k5_partfun1(A_9417, B_9418, C_9419)=D_9420 | ~m1_subset_1(C_9419, k1_zfmisc_1(k2_zfmisc_1(A_9417, B_9418))) | ~v1_funct_1(C_9419))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_8747, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')) | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_6306, c_8733])).
% 9.45/3.12  tff(c_8764, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_5612, c_7530, c_5606, c_8747])).
% 9.45/3.12  tff(c_8765, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_62, c_8764])).
% 9.45/3.12  tff(c_8409, plain, (![A_9404, B_9405, C_9406, D_9407]: ('#skF_2'(A_9404, B_9405, C_9406, D_9407)='#skF_1'(A_9404, B_9405, C_9406, D_9407) | ~r1_partfun1(C_9406, '#skF_3'(A_9404, B_9405, C_9406, D_9407)) | ~v1_partfun1('#skF_3'(A_9404, B_9405, C_9406, D_9407), A_9404) | ~m1_subset_1('#skF_3'(A_9404, B_9405, C_9406, D_9407), k1_zfmisc_1(k2_zfmisc_1(A_9404, B_9405))) | ~v1_funct_1('#skF_3'(A_9404, B_9405, C_9406, D_9407)) | k5_partfun1(A_9404, B_9405, C_9406)=D_9407 | ~m1_subset_1(C_9406, k1_zfmisc_1(k2_zfmisc_1(A_9404, B_9405))) | ~v1_funct_1(C_9406))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_8423, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')) | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_6306, c_8409])).
% 9.45/3.12  tff(c_8440, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_5612, c_7530, c_5606, c_8423])).
% 9.45/3.12  tff(c_8441, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))='#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_62, c_8440])).
% 9.45/3.12  tff(c_2676, plain, (v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_2673, c_2635])).
% 9.45/3.12  tff(c_2688, plain, (v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_62, c_2676])).
% 9.45/3.12  tff(c_5614, plain, (v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_5597, c_2688])).
% 9.45/3.12  tff(c_5615, plain, (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_5614])).
% 9.45/3.12  tff(c_8451, plain, (v1_funct_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_8441, c_5615])).
% 9.45/3.12  tff(c_8231, plain, (![A_9398, B_9399, C_9400, D_9401]: (m1_subset_1('#skF_2'(A_9398, B_9399, C_9400, D_9401), k1_zfmisc_1(k2_zfmisc_1(A_9398, B_9399))) | ~r1_partfun1(C_9400, '#skF_3'(A_9398, B_9399, C_9400, D_9401)) | ~v1_partfun1('#skF_3'(A_9398, B_9399, C_9400, D_9401), A_9398) | ~m1_subset_1('#skF_3'(A_9398, B_9399, C_9400, D_9401), k1_zfmisc_1(k2_zfmisc_1(A_9398, B_9399))) | ~v1_funct_1('#skF_3'(A_9398, B_9399, C_9400, D_9401)) | k5_partfun1(A_9398, B_9399, C_9400)=D_9401 | ~m1_subset_1(C_9400, k1_zfmisc_1(k2_zfmisc_1(A_9398, B_9399))) | ~v1_funct_1(C_9400))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_8242, plain, (m1_subset_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_6306, c_8231])).
% 9.45/3.12  tff(c_8256, plain, (m1_subset_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_5612, c_7530, c_5606, c_8242])).
% 9.45/3.12  tff(c_8257, plain, (m1_subset_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_8256])).
% 9.45/3.12  tff(c_8448, plain, (m1_subset_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_8441, c_8257])).
% 9.45/3.12  tff(c_8514, plain, (![C_52]: (r1_partfun1(C_52, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_funct_1('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_52))), inference(resolution, [status(thm)], [c_8448, c_52])).
% 9.45/3.12  tff(c_8562, plain, (![C_52]: (r1_partfun1(C_52, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_52))), inference(demodulation, [status(thm), theory('equality')], [c_8451, c_8514])).
% 9.45/3.12  tff(c_2523, plain, (![C_8984, D_8985, A_8986, B_8987]: (r1_partfun1(C_8984, D_8985) | ~m1_subset_1(D_8985, k1_zfmisc_1(k2_zfmisc_1(A_8986, k1_tarski(B_8987)))) | ~v1_funct_1(D_8985) | ~m1_subset_1(C_8984, k1_zfmisc_1(k2_zfmisc_1(A_8986, k1_tarski(B_8987)))) | ~v1_funct_1(C_8984))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.45/3.12  tff(c_2527, plain, (![C_8984]: (r1_partfun1(C_8984, '#skF_8') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_8984, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_8984))), inference(resolution, [status(thm)], [c_64, c_2523])).
% 9.45/3.12  tff(c_2536, plain, (![C_8984]: (r1_partfun1(C_8984, '#skF_8') | ~m1_subset_1(C_8984, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_8984))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2527])).
% 9.45/3.12  tff(c_8283, plain, (r1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_8') | ~v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_8257, c_2536])).
% 9.45/3.12  tff(c_8330, plain, (r1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5615, c_8283])).
% 9.45/3.12  tff(c_7529, plain, (v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5')), inference(splitRight, [status(thm)], [c_7520])).
% 9.45/3.12  tff(c_60, plain, (![A_60, B_61, C_62]: (k5_partfun1(A_60, B_61, C_62)=k1_tarski(C_62) | ~v1_partfun1(C_62, A_60) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_1(C_62))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.45/3.12  tff(c_8291, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))=k1_tarski('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_8257, c_60])).
% 9.45/3.12  tff(c_8339, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))=k1_tarski('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_5615, c_7529, c_8291])).
% 9.45/3.12  tff(c_2507, plain, (v1_partfun1('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_157])).
% 9.45/3.12  tff(c_6188, plain, (![F_9284, A_9285, B_9286, C_9287]: (r2_hidden(F_9284, k5_partfun1(A_9285, B_9286, C_9287)) | ~r1_partfun1(C_9287, F_9284) | ~v1_partfun1(F_9284, A_9285) | ~m1_subset_1(F_9284, k1_zfmisc_1(k2_zfmisc_1(A_9285, B_9286))) | ~v1_funct_1(F_9284) | ~m1_subset_1(C_9287, k1_zfmisc_1(k2_zfmisc_1(A_9285, B_9286))) | ~v1_funct_1(C_9287))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_6198, plain, (![C_9287]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_9287)) | ~r1_partfun1(C_9287, '#skF_8') | ~v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_9287, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_9287))), inference(resolution, [status(thm)], [c_64, c_6188])).
% 9.45/3.12  tff(c_6478, plain, (![C_9295]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_9295)) | ~r1_partfun1(C_9295, '#skF_8') | ~m1_subset_1(C_9295, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_9295))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2507, c_6198])).
% 9.45/3.12  tff(c_6495, plain, (![E_8994]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', k1_tarski('#skF_6'), E_8994)) | ~r1_partfun1(E_8994, '#skF_8') | ~v1_funct_1(E_8994) | ~r2_hidden(E_8994, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_5886, c_6478])).
% 9.45/3.12  tff(c_8377, plain, (r2_hidden('#skF_8', k1_tarski('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))) | ~r1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_8') | ~v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8339, c_6495])).
% 9.45/3.12  tff(c_8398, plain, (r2_hidden('#skF_8', k1_tarski('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))) | ~r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5615, c_8330, c_8377])).
% 9.45/3.12  tff(c_8408, plain, (~r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_8398])).
% 9.45/3.12  tff(c_8442, plain, (~r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_8441, c_8408])).
% 9.45/3.12  tff(c_8270, plain, (![C_10]: (r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_10)) | ~r1_partfun1(C_10, '#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_partfun1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_10))), inference(resolution, [status(thm)], [c_8257, c_16])).
% 9.45/3.12  tff(c_8312, plain, (![C_10]: (r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_10)) | ~r1_partfun1(C_10, '#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_10))), inference(demodulation, [status(thm), theory('equality')], [c_5615, c_7529, c_8270])).
% 9.45/3.12  tff(c_8655, plain, (![C_9416]: (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k5_partfun1('#skF_5', k1_tarski('#skF_6'), C_9416)) | ~r1_partfun1(C_9416, '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1(C_9416, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_9416))), inference(demodulation, [status(thm), theory('equality')], [c_8441, c_8441, c_8312])).
% 9.45/3.12  tff(c_8666, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | ~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2508, c_8655])).
% 9.45/3.12  tff(c_8673, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8')) | ~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_8666])).
% 9.45/3.12  tff(c_8674, plain, (~r1_partfun1('#skF_8', '#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_8442, c_8673])).
% 9.45/3.12  tff(c_8677, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_8562, c_8674])).
% 9.45/3.12  tff(c_8681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_8677])).
% 9.45/3.12  tff(c_8683, plain, (r2_hidden('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_8398])).
% 9.45/3.12  tff(c_8767, plain, (r2_hidden('#skF_1'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_8765, c_8683])).
% 9.45/3.12  tff(c_28, plain, (![A_8, B_9, C_10, D_32]: (~r2_hidden('#skF_1'(A_8, B_9, C_10, D_32), D_32) | ~r1_partfun1(C_10, '#skF_3'(A_8, B_9, C_10, D_32)) | ~v1_partfun1('#skF_3'(A_8, B_9, C_10, D_32), A_8) | ~m1_subset_1('#skF_3'(A_8, B_9, C_10, D_32), k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1('#skF_3'(A_8, B_9, C_10, D_32)) | k5_partfun1(A_8, B_9, C_10)=D_32 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_8811, plain, (~r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_8767, c_28])).
% 9.45/3.12  tff(c_8837, plain, (k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_5612, c_7530, c_5606, c_6306, c_8811])).
% 9.45/3.12  tff(c_8839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_8837])).
% 9.45/3.12  tff(c_8841, plain, (~v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_5614])).
% 9.45/3.12  tff(c_8840, plain, (v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5')), inference(splitRight, [status(thm)], [c_5614])).
% 9.45/3.12  tff(c_9299, plain, (![E_9473]: (m1_subset_1(E_9473, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~r2_hidden(E_9473, k1_tarski('#skF_8')) | ~r2_hidden(E_9473, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2570, c_9254])).
% 9.45/3.12  tff(c_9746, plain, (![C_9482, E_9483]: (r1_partfun1(C_9482, E_9483) | ~v1_funct_1(E_9483) | ~m1_subset_1(C_9482, k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1(C_9482) | ~r2_hidden(E_9483, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_9299, c_52])).
% 9.45/3.12  tff(c_9758, plain, (![E_9483]: (r1_partfun1('#skF_7', E_9483) | ~v1_funct_1(E_9483) | ~v1_funct_1('#skF_7') | ~r2_hidden(E_9483, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_70, c_9746])).
% 9.45/3.12  tff(c_9771, plain, (![E_9484]: (r1_partfun1('#skF_7', E_9484) | ~v1_funct_1(E_9484) | ~r2_hidden(E_9484, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_9758])).
% 9.45/3.12  tff(c_9839, plain, (r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(resolution, [status(thm)], [c_2649, c_9771])).
% 9.45/3.12  tff(c_9878, plain, (r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5612, c_9839])).
% 9.45/3.12  tff(c_9879, plain, (r1_partfun1('#skF_7', '#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_62, c_8841, c_9878])).
% 9.45/3.12  tff(c_10364, plain, (![A_9502, B_9503, C_9504, D_9505]: (v1_funct_1('#skF_2'(A_9502, B_9503, C_9504, D_9505)) | ~r1_partfun1(C_9504, '#skF_3'(A_9502, B_9503, C_9504, D_9505)) | ~v1_partfun1('#skF_3'(A_9502, B_9503, C_9504, D_9505), A_9502) | ~m1_subset_1('#skF_3'(A_9502, B_9503, C_9504, D_9505), k1_zfmisc_1(k2_zfmisc_1(A_9502, B_9503))) | ~v1_funct_1('#skF_3'(A_9502, B_9503, C_9504, D_9505)) | k5_partfun1(A_9502, B_9503, C_9504)=D_9505 | ~m1_subset_1(C_9504, k1_zfmisc_1(k2_zfmisc_1(A_9502, B_9503))) | ~v1_funct_1(C_9504))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.45/3.12  tff(c_10369, plain, (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~v1_partfun1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_9879, c_10364])).
% 9.45/3.12  tff(c_10376, plain, (v1_funct_1('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8'))) | ~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))) | k5_partfun1('#skF_5', k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_5612, c_8840, c_10369])).
% 9.45/3.12  tff(c_10377, plain, (~m1_subset_1('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_8841, c_10376])).
% 9.45/3.12  tff(c_10380, plain, (~r2_hidden('#skF_3'('#skF_5', k1_tarski('#skF_6'), '#skF_7', k1_tarski('#skF_8')), k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_9286, c_10377])).
% 9.45/3.12  tff(c_10384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5597, c_10380])).
% 9.45/3.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.45/3.12  
% 9.45/3.12  Inference rules
% 9.45/3.12  ----------------------
% 9.45/3.12  #Ref     : 0
% 9.45/3.12  #Sup     : 2504
% 9.45/3.12  #Fact    : 0
% 9.45/3.12  #Define  : 0
% 9.45/3.12  #Split   : 12
% 9.45/3.12  #Chain   : 0
% 9.45/3.12  #Close   : 0
% 9.45/3.12  
% 9.45/3.12  Ordering : KBO
% 9.45/3.12  
% 9.45/3.12  Simplification rules
% 9.45/3.12  ----------------------
% 9.45/3.12  #Subsume      : 167
% 9.45/3.12  #Demod        : 1223
% 9.45/3.12  #Tautology    : 492
% 9.45/3.12  #SimpNegUnit  : 180
% 9.45/3.12  #BackRed      : 47
% 9.45/3.12  
% 9.45/3.12  #Partial instantiations: 600
% 9.45/3.12  #Strategies tried      : 1
% 9.45/3.12  
% 9.45/3.12  Timing (in seconds)
% 9.45/3.12  ----------------------
% 9.45/3.12  Preprocessing        : 0.34
% 9.45/3.12  Parsing              : 0.16
% 9.45/3.12  CNF conversion       : 0.03
% 9.45/3.12  Main loop            : 1.99
% 9.45/3.12  Inferencing          : 0.71
% 9.45/3.12  Reduction            : 0.63
% 9.45/3.12  Demodulation         : 0.44
% 9.45/3.12  BG Simplification    : 0.09
% 9.45/3.12  Subsumption          : 0.40
% 9.45/3.12  Abstraction          : 0.13
% 9.45/3.12  MUC search           : 0.00
% 9.45/3.12  Cooper               : 0.00
% 9.45/3.12  Total                : 2.40
% 9.45/3.12  Index Insertion      : 0.00
% 9.45/3.12  Index Deletion       : 0.00
% 9.45/3.12  Index Matching       : 0.00
% 9.45/3.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
