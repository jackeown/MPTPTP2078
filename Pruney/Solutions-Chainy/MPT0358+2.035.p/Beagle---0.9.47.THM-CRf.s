%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:04 EST 2020

% Result     : Theorem 4.29s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 138 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 204 expanded)
%              Number of equality atoms :   31 (  84 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_94,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_58,plain,(
    ! [A_26] : k1_subset_1(A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_72,plain,
    ( k1_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_82,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_72])).

tff(c_128,plain,(
    ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_78,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_81,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_78])).

tff(c_155,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_81])).

tff(c_68,plain,(
    ! [A_32] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_160,plain,(
    ! [A_32] : m1_subset_1('#skF_7',k1_zfmisc_1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_68])).

tff(c_64,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_380,plain,(
    ! [B_82,A_83] :
      ( r2_hidden(B_82,A_83)
      | ~ m1_subset_1(B_82,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_401,plain,(
    ! [B_82,A_19] :
      ( r1_tarski(B_82,A_19)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_380,c_38])).

tff(c_410,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(B_84,A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_401])).

tff(c_423,plain,(
    ! [A_32] : r1_tarski('#skF_7',A_32) ),
    inference(resolution,[status(thm)],[c_160,c_410])).

tff(c_60,plain,(
    ! [A_27] : k2_subset_1(A_27) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_66,plain,(
    ! [A_31] : k3_subset_1(A_31,k1_subset_1(A_31)) = k2_subset_1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_79,plain,(
    ! [A_31] : k3_subset_1(A_31,k1_subset_1(A_31)) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_66])).

tff(c_80,plain,(
    ! [A_31] : k3_subset_1(A_31,k1_xboole_0) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_79])).

tff(c_159,plain,(
    ! [A_31] : k3_subset_1(A_31,'#skF_7') = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_80])).

tff(c_182,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_128])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_182])).

tff(c_428,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_430,plain,(
    ! [A_87,B_88] :
      ( k3_xboole_0(A_87,B_88) = A_87
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_437,plain,(
    k3_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_428,c_430])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_513,plain,(
    ! [D_103,B_104,A_105] :
      ( ~ r2_hidden(D_103,B_104)
      | ~ r2_hidden(D_103,k4_xboole_0(A_105,B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1655,plain,(
    ! [D_177,A_178,B_179] :
      ( ~ r2_hidden(D_177,k4_xboole_0(A_178,B_179))
      | ~ r2_hidden(D_177,k3_xboole_0(A_178,B_179)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_513])).

tff(c_2769,plain,(
    ! [D_218,A_219,B_220] :
      ( ~ r2_hidden(D_218,k3_xboole_0(A_219,B_220))
      | r2_hidden(D_218,B_220)
      | ~ r2_hidden(D_218,A_219) ) ),
    inference(resolution,[status(thm)],[c_2,c_1655])).

tff(c_2997,plain,(
    ! [D_224] :
      ( ~ r2_hidden(D_224,'#skF_7')
      | r2_hidden(D_224,k3_subset_1('#skF_6','#skF_7'))
      | ~ r2_hidden(D_224,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_2769])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_801,plain,(
    ! [A_129,B_130] :
      ( k4_xboole_0(A_129,B_130) = k3_subset_1(A_129,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_817,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_801])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_823,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | ~ r2_hidden(D_6,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_817,c_4])).

tff(c_3030,plain,(
    ! [D_224] : ~ r2_hidden(D_224,'#skF_7') ),
    inference(resolution,[status(thm)],[c_2997,c_823])).

tff(c_427,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_504,plain,(
    ! [D_100,A_101,B_102] :
      ( r2_hidden(D_100,A_101)
      | ~ r2_hidden(D_100,k4_xboole_0(A_101,B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1263,plain,(
    ! [D_153,A_154,B_155] :
      ( r2_hidden(D_153,A_154)
      | ~ r2_hidden(D_153,k3_xboole_0(A_154,B_155)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_504])).

tff(c_2105,plain,(
    ! [A_191,B_192] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_191,B_192)),A_191)
      | k3_xboole_0(A_191,B_192) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_1263])).

tff(c_2163,plain,
    ( r2_hidden('#skF_3'('#skF_7'),'#skF_7')
    | k3_xboole_0('#skF_7',k3_subset_1('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_2105])).

tff(c_2189,plain,
    ( r2_hidden('#skF_3'('#skF_7'),'#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_2163])).

tff(c_2190,plain,(
    r2_hidden('#skF_3'('#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_2189])).

tff(c_3035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3030,c_2190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:28:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.29/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.82  
% 4.29/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.82  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 4.39/1.82  
% 4.39/1.82  %Foreground sorts:
% 4.39/1.82  
% 4.39/1.82  
% 4.39/1.82  %Background operators:
% 4.39/1.82  
% 4.39/1.82  
% 4.39/1.82  %Foreground operators:
% 4.39/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.39/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.39/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.39/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.39/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.39/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.39/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.39/1.82  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.39/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.39/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.39/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.39/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.82  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.39/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.82  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.39/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.39/1.82  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.39/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.39/1.82  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.39/1.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.39/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.39/1.82  
% 4.40/1.83  tff(f_83, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 4.40/1.83  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 4.40/1.83  tff(f_96, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.40/1.83  tff(f_92, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.40/1.83  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.40/1.83  tff(f_68, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.40/1.83  tff(f_85, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.40/1.83  tff(f_94, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 4.40/1.83  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.40/1.83  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.40/1.83  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.40/1.83  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.40/1.83  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.40/1.83  tff(c_58, plain, (![A_26]: (k1_subset_1(A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.40/1.83  tff(c_72, plain, (k1_subset_1('#skF_6')!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.40/1.83  tff(c_82, plain, (k1_xboole_0!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_72])).
% 4.40/1.83  tff(c_128, plain, (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_82])).
% 4.40/1.83  tff(c_78, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.40/1.83  tff(c_81, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_78])).
% 4.40/1.83  tff(c_155, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_128, c_81])).
% 4.40/1.83  tff(c_68, plain, (![A_32]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.40/1.83  tff(c_160, plain, (![A_32]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_68])).
% 4.40/1.83  tff(c_64, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.40/1.83  tff(c_380, plain, (![B_82, A_83]: (r2_hidden(B_82, A_83) | ~m1_subset_1(B_82, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.40/1.83  tff(c_38, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.40/1.83  tff(c_401, plain, (![B_82, A_19]: (r1_tarski(B_82, A_19) | ~m1_subset_1(B_82, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_380, c_38])).
% 4.40/1.83  tff(c_410, plain, (![B_84, A_85]: (r1_tarski(B_84, A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)))), inference(negUnitSimplification, [status(thm)], [c_64, c_401])).
% 4.40/1.83  tff(c_423, plain, (![A_32]: (r1_tarski('#skF_7', A_32))), inference(resolution, [status(thm)], [c_160, c_410])).
% 4.40/1.83  tff(c_60, plain, (![A_27]: (k2_subset_1(A_27)=A_27)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.40/1.83  tff(c_66, plain, (![A_31]: (k3_subset_1(A_31, k1_subset_1(A_31))=k2_subset_1(A_31))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.40/1.83  tff(c_79, plain, (![A_31]: (k3_subset_1(A_31, k1_subset_1(A_31))=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_66])).
% 4.40/1.83  tff(c_80, plain, (![A_31]: (k3_subset_1(A_31, k1_xboole_0)=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_79])).
% 4.40/1.83  tff(c_159, plain, (![A_31]: (k3_subset_1(A_31, '#skF_7')=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_80])).
% 4.40/1.83  tff(c_182, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_128])).
% 4.40/1.83  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_423, c_182])).
% 4.40/1.83  tff(c_428, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_82])).
% 4.40/1.83  tff(c_430, plain, (![A_87, B_88]: (k3_xboole_0(A_87, B_88)=A_87 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.40/1.83  tff(c_437, plain, (k3_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_428, c_430])).
% 4.40/1.83  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.40/1.83  tff(c_34, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.40/1.83  tff(c_513, plain, (![D_103, B_104, A_105]: (~r2_hidden(D_103, B_104) | ~r2_hidden(D_103, k4_xboole_0(A_105, B_104)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.40/1.83  tff(c_1655, plain, (![D_177, A_178, B_179]: (~r2_hidden(D_177, k4_xboole_0(A_178, B_179)) | ~r2_hidden(D_177, k3_xboole_0(A_178, B_179)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_513])).
% 4.40/1.83  tff(c_2769, plain, (![D_218, A_219, B_220]: (~r2_hidden(D_218, k3_xboole_0(A_219, B_220)) | r2_hidden(D_218, B_220) | ~r2_hidden(D_218, A_219))), inference(resolution, [status(thm)], [c_2, c_1655])).
% 4.40/1.83  tff(c_2997, plain, (![D_224]: (~r2_hidden(D_224, '#skF_7') | r2_hidden(D_224, k3_subset_1('#skF_6', '#skF_7')) | ~r2_hidden(D_224, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_437, c_2769])).
% 4.40/1.83  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.40/1.83  tff(c_801, plain, (![A_129, B_130]: (k4_xboole_0(A_129, B_130)=k3_subset_1(A_129, B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.40/1.83  tff(c_817, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_801])).
% 4.40/1.83  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.40/1.83  tff(c_823, plain, (![D_6]: (~r2_hidden(D_6, '#skF_7') | ~r2_hidden(D_6, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_817, c_4])).
% 4.40/1.83  tff(c_3030, plain, (![D_224]: (~r2_hidden(D_224, '#skF_7'))), inference(resolution, [status(thm)], [c_2997, c_823])).
% 4.40/1.83  tff(c_427, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_82])).
% 4.40/1.83  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.40/1.83  tff(c_504, plain, (![D_100, A_101, B_102]: (r2_hidden(D_100, A_101) | ~r2_hidden(D_100, k4_xboole_0(A_101, B_102)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.40/1.83  tff(c_1263, plain, (![D_153, A_154, B_155]: (r2_hidden(D_153, A_154) | ~r2_hidden(D_153, k3_xboole_0(A_154, B_155)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_504])).
% 4.40/1.83  tff(c_2105, plain, (![A_191, B_192]: (r2_hidden('#skF_3'(k3_xboole_0(A_191, B_192)), A_191) | k3_xboole_0(A_191, B_192)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_1263])).
% 4.40/1.83  tff(c_2163, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_7') | k3_xboole_0('#skF_7', k3_subset_1('#skF_6', '#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_437, c_2105])).
% 4.40/1.83  tff(c_2189, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_437, c_2163])).
% 4.40/1.83  tff(c_2190, plain, (r2_hidden('#skF_3'('#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_427, c_2189])).
% 4.40/1.83  tff(c_3035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3030, c_2190])).
% 4.40/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.83  
% 4.40/1.83  Inference rules
% 4.40/1.83  ----------------------
% 4.40/1.83  #Ref     : 0
% 4.40/1.83  #Sup     : 644
% 4.40/1.83  #Fact    : 0
% 4.40/1.83  #Define  : 0
% 4.40/1.83  #Split   : 10
% 4.40/1.83  #Chain   : 0
% 4.40/1.83  #Close   : 0
% 4.40/1.83  
% 4.40/1.83  Ordering : KBO
% 4.40/1.83  
% 4.40/1.83  Simplification rules
% 4.40/1.83  ----------------------
% 4.40/1.83  #Subsume      : 90
% 4.40/1.83  #Demod        : 189
% 4.40/1.83  #Tautology    : 236
% 4.40/1.83  #SimpNegUnit  : 54
% 4.40/1.83  #BackRed      : 22
% 4.40/1.83  
% 4.40/1.83  #Partial instantiations: 0
% 4.40/1.83  #Strategies tried      : 1
% 4.40/1.83  
% 4.40/1.83  Timing (in seconds)
% 4.40/1.83  ----------------------
% 4.40/1.84  Preprocessing        : 0.30
% 4.40/1.84  Parsing              : 0.15
% 4.40/1.84  CNF conversion       : 0.02
% 4.40/1.84  Main loop            : 0.68
% 4.40/1.84  Inferencing          : 0.23
% 4.40/1.84  Reduction            : 0.22
% 4.40/1.84  Demodulation         : 0.16
% 4.40/1.84  BG Simplification    : 0.03
% 4.40/1.84  Subsumption          : 0.14
% 4.40/1.84  Abstraction          : 0.03
% 4.40/1.84  MUC search           : 0.00
% 4.40/1.84  Cooper               : 0.00
% 4.40/1.84  Total                : 1.02
% 4.40/1.84  Index Insertion      : 0.00
% 4.40/1.84  Index Deletion       : 0.00
% 4.40/1.84  Index Matching       : 0.00
% 4.40/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
