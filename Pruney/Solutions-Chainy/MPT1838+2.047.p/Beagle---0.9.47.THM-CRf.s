%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:20 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 221 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :  140 ( 516 expanded)
%              Number of equality atoms :   60 ( 236 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    ! [A_17] :
      ( m1_subset_1('#skF_1'(A_17),A_17)
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_339,plain,(
    ! [A_63,B_64] :
      ( k6_domain_1(A_63,B_64) = k1_tarski(B_64)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_369,plain,(
    ! [A_73] :
      ( k6_domain_1(A_73,'#skF_1'(A_73)) = k1_tarski('#skF_1'(A_73))
      | ~ v1_zfmisc_1(A_73)
      | v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_24,c_339])).

tff(c_22,plain,(
    ! [A_17] :
      ( k6_domain_1(A_17,'#skF_1'(A_17)) = A_17
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_384,plain,(
    ! [A_74] :
      ( k1_tarski('#skF_1'(A_74)) = A_74
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74)
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_22])).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_55,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_353,plain,(
    ! [C_67,B_68,A_69] :
      ( k1_xboole_0 = C_67
      | k1_xboole_0 = B_68
      | C_67 = B_68
      | k2_xboole_0(B_68,C_67) != k1_tarski(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_359,plain,(
    ! [A_69] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | '#skF_2' = '#skF_3'
      | k1_tarski(A_69) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_353])).

tff(c_361,plain,(
    ! [A_69] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_tarski(A_69) != '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_359])).

tff(c_362,plain,(
    ! [A_69] : k1_tarski(A_69) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_404,plain,(
    ! [A_75] :
      ( A_75 != '#skF_3'
      | ~ v1_zfmisc_1(A_75)
      | v1_xboole_0(A_75)
      | ~ v1_zfmisc_1(A_75)
      | v1_xboole_0(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_362])).

tff(c_406,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_404])).

tff(c_409,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_406])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_409])).

tff(c_412,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_413,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_117,plain,(
    ! [A_40,B_41] :
      ( k6_domain_1(A_40,B_41) = k1_tarski(B_41)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_148,plain,(
    ! [A_52] :
      ( k6_domain_1(A_52,'#skF_1'(A_52)) = k1_tarski('#skF_1'(A_52))
      | ~ v1_zfmisc_1(A_52)
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_24,c_117])).

tff(c_163,plain,(
    ! [A_53] :
      ( k1_tarski('#skF_1'(A_53)) = A_53
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53)
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_22])).

tff(c_141,plain,(
    ! [C_48,B_49,A_50] :
      ( k1_xboole_0 = C_48
      | k1_xboole_0 = B_49
      | C_48 = B_49
      | k2_xboole_0(B_49,C_48) != k1_tarski(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_144,plain,(
    ! [A_50] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | '#skF_2' = '#skF_3'
      | k1_tarski(A_50) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_141])).

tff(c_145,plain,(
    ! [A_50] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_tarski(A_50) != '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_144])).

tff(c_146,plain,(
    ! [A_50] : k1_tarski(A_50) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_183,plain,(
    ! [A_54] :
      ( A_54 != '#skF_3'
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54)
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_146])).

tff(c_185,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_183])).

tff(c_188,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_185])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_188])).

tff(c_191,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_207,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_39,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_218,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_47])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [B_33,A_34] :
      ( ~ r1_xboole_0(B_33,A_34)
      | ~ r1_tarski(B_33,A_34)
      | v1_xboole_0(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [A_35] :
      ( ~ r1_tarski(A_35,k1_xboole_0)
      | v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_8,c_69])).

tff(c_93,plain,(
    ! [A_36] :
      ( v1_xboole_0(A_36)
      | k4_xboole_0(A_36,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_101,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_34])).

tff(c_211,plain,(
    k4_xboole_0('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_207,c_101])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_211])).

tff(c_253,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_xboole_0(k4_xboole_0(A_8,B_9),B_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    r1_xboole_0(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_12])).

tff(c_79,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_3')
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_51,c_69])).

tff(c_88,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_262,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_88])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_262])).

tff(c_272,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_428,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_272])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_428])).

tff(c_437,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_448,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_272])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.75  
% 2.83/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.76  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.83/1.76  
% 2.83/1.76  %Foreground sorts:
% 2.83/1.76  
% 2.83/1.76  
% 2.83/1.76  %Background operators:
% 2.83/1.76  
% 2.83/1.76  
% 2.83/1.76  %Foreground operators:
% 2.83/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.76  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.83/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.83/1.76  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.76  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.76  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.83/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.76  
% 3.13/1.78  tff(f_93, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.13/1.78  tff(f_79, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 3.13/1.78  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.13/1.78  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.13/1.78  tff(f_62, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.13/1.78  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.13/1.78  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.13/1.78  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.13/1.78  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.13/1.78  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.78  tff(c_32, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.78  tff(c_30, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.78  tff(c_24, plain, (![A_17]: (m1_subset_1('#skF_1'(A_17), A_17) | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.13/1.78  tff(c_339, plain, (![A_63, B_64]: (k6_domain_1(A_63, B_64)=k1_tarski(B_64) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.78  tff(c_369, plain, (![A_73]: (k6_domain_1(A_73, '#skF_1'(A_73))=k1_tarski('#skF_1'(A_73)) | ~v1_zfmisc_1(A_73) | v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_24, c_339])).
% 3.13/1.78  tff(c_22, plain, (![A_17]: (k6_domain_1(A_17, '#skF_1'(A_17))=A_17 | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.13/1.78  tff(c_384, plain, (![A_74]: (k1_tarski('#skF_1'(A_74))=A_74 | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74) | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74))), inference(superposition, [status(thm), theory('equality')], [c_369, c_22])).
% 3.13/1.78  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.78  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.13/1.78  tff(c_55, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.13/1.78  tff(c_63, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_55])).
% 3.13/1.78  tff(c_353, plain, (![C_67, B_68, A_69]: (k1_xboole_0=C_67 | k1_xboole_0=B_68 | C_67=B_68 | k2_xboole_0(B_68, C_67)!=k1_tarski(A_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.13/1.78  tff(c_359, plain, (![A_69]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | '#skF_2'='#skF_3' | k1_tarski(A_69)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_63, c_353])).
% 3.13/1.78  tff(c_361, plain, (![A_69]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_tarski(A_69)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_359])).
% 3.13/1.78  tff(c_362, plain, (![A_69]: (k1_tarski(A_69)!='#skF_3')), inference(splitLeft, [status(thm)], [c_361])).
% 3.13/1.78  tff(c_404, plain, (![A_75]: (A_75!='#skF_3' | ~v1_zfmisc_1(A_75) | v1_xboole_0(A_75) | ~v1_zfmisc_1(A_75) | v1_xboole_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_384, c_362])).
% 3.13/1.78  tff(c_406, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_404])).
% 3.13/1.78  tff(c_409, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_406])).
% 3.13/1.78  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_409])).
% 3.13/1.78  tff(c_412, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_361])).
% 3.13/1.78  tff(c_413, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_412])).
% 3.13/1.78  tff(c_117, plain, (![A_40, B_41]: (k6_domain_1(A_40, B_41)=k1_tarski(B_41) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.13/1.78  tff(c_148, plain, (![A_52]: (k6_domain_1(A_52, '#skF_1'(A_52))=k1_tarski('#skF_1'(A_52)) | ~v1_zfmisc_1(A_52) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_24, c_117])).
% 3.13/1.78  tff(c_163, plain, (![A_53]: (k1_tarski('#skF_1'(A_53))=A_53 | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(superposition, [status(thm), theory('equality')], [c_148, c_22])).
% 3.13/1.78  tff(c_141, plain, (![C_48, B_49, A_50]: (k1_xboole_0=C_48 | k1_xboole_0=B_49 | C_48=B_49 | k2_xboole_0(B_49, C_48)!=k1_tarski(A_50))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.13/1.78  tff(c_144, plain, (![A_50]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | '#skF_2'='#skF_3' | k1_tarski(A_50)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_63, c_141])).
% 3.13/1.78  tff(c_145, plain, (![A_50]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_tarski(A_50)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_144])).
% 3.13/1.78  tff(c_146, plain, (![A_50]: (k1_tarski(A_50)!='#skF_3')), inference(splitLeft, [status(thm)], [c_145])).
% 3.13/1.78  tff(c_183, plain, (![A_54]: (A_54!='#skF_3' | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54) | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54))), inference(superposition, [status(thm), theory('equality')], [c_163, c_146])).
% 3.13/1.78  tff(c_185, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_183])).
% 3.13/1.78  tff(c_188, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_185])).
% 3.13/1.78  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_188])).
% 3.13/1.78  tff(c_191, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_145])).
% 3.13/1.78  tff(c_207, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_191])).
% 3.13/1.78  tff(c_39, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.78  tff(c_47, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_39])).
% 3.13/1.78  tff(c_218, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_207, c_47])).
% 3.13/1.78  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.78  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.78  tff(c_69, plain, (![B_33, A_34]: (~r1_xboole_0(B_33, A_34) | ~r1_tarski(B_33, A_34) | v1_xboole_0(B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.78  tff(c_82, plain, (![A_35]: (~r1_tarski(A_35, k1_xboole_0) | v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_8, c_69])).
% 3.13/1.78  tff(c_93, plain, (![A_36]: (v1_xboole_0(A_36) | k4_xboole_0(A_36, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_82])).
% 3.13/1.78  tff(c_101, plain, (k4_xboole_0('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_93, c_34])).
% 3.13/1.78  tff(c_211, plain, (k4_xboole_0('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_207, c_207, c_101])).
% 3.13/1.78  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_218, c_211])).
% 3.13/1.78  tff(c_253, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_191])).
% 3.13/1.78  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(k4_xboole_0(A_8, B_9), B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.13/1.78  tff(c_51, plain, (r1_xboole_0(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_47, c_12])).
% 3.13/1.78  tff(c_79, plain, (~r1_tarski(k1_xboole_0, '#skF_3') | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_51, c_69])).
% 3.13/1.78  tff(c_88, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_79])).
% 3.13/1.78  tff(c_262, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_88])).
% 3.13/1.78  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_262])).
% 3.13/1.78  tff(c_272, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_79])).
% 3.13/1.78  tff(c_428, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_272])).
% 3.13/1.78  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_428])).
% 3.13/1.78  tff(c_437, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_412])).
% 3.13/1.78  tff(c_448, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_437, c_272])).
% 3.13/1.78  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_448])).
% 3.13/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.78  
% 3.13/1.78  Inference rules
% 3.13/1.78  ----------------------
% 3.13/1.78  #Ref     : 0
% 3.13/1.78  #Sup     : 82
% 3.13/1.78  #Fact    : 0
% 3.13/1.78  #Define  : 0
% 3.13/1.78  #Split   : 5
% 3.13/1.78  #Chain   : 0
% 3.13/1.78  #Close   : 0
% 3.13/1.78  
% 3.13/1.78  Ordering : KBO
% 3.13/1.78  
% 3.13/1.78  Simplification rules
% 3.13/1.78  ----------------------
% 3.13/1.78  #Subsume      : 4
% 3.13/1.78  #Demod        : 107
% 3.13/1.78  #Tautology    : 43
% 3.13/1.78  #SimpNegUnit  : 8
% 3.13/1.78  #BackRed      : 60
% 3.13/1.78  
% 3.13/1.78  #Partial instantiations: 0
% 3.13/1.78  #Strategies tried      : 1
% 3.13/1.78  
% 3.13/1.78  Timing (in seconds)
% 3.13/1.78  ----------------------
% 3.13/1.79  Preprocessing        : 0.46
% 3.13/1.79  Parsing              : 0.23
% 3.13/1.79  CNF conversion       : 0.03
% 3.13/1.79  Main loop            : 0.41
% 3.13/1.79  Inferencing          : 0.15
% 3.13/1.79  Reduction            : 0.13
% 3.13/1.79  Demodulation         : 0.09
% 3.13/1.79  BG Simplification    : 0.03
% 3.13/1.79  Subsumption          : 0.06
% 3.13/1.79  Abstraction          : 0.02
% 3.13/1.79  MUC search           : 0.00
% 3.13/1.79  Cooper               : 0.00
% 3.13/1.79  Total                : 0.93
% 3.13/1.79  Index Insertion      : 0.00
% 3.13/1.79  Index Deletion       : 0.00
% 3.13/1.79  Index Matching       : 0.00
% 3.13/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
