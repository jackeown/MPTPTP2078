%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:19 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   59 (  66 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  75 expanded)
%              Number of equality atoms :   28 (  35 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1042,plain,(
    ! [A_98,B_99] :
      ( k4_xboole_0(A_98,B_99) = k3_subset_1(A_98,B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1055,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1042])).

tff(c_24,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_743,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_xboole_0(A_85,C_86)
      | ~ r1_xboole_0(B_87,C_86)
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1531,plain,(
    ! [A_116,B_117,A_118] :
      ( r1_xboole_0(A_116,B_117)
      | ~ r1_tarski(A_116,k4_xboole_0(A_118,B_117)) ) ),
    inference(resolution,[status(thm)],[c_24,c_743])).

tff(c_2012,plain,(
    ! [A_129] :
      ( r1_xboole_0(A_129,'#skF_5')
      | ~ r1_tarski(A_129,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_1531])).

tff(c_2025,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_2012])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2144,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2025,c_26])).

tff(c_16,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_566,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_621,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_566])).

tff(c_631,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_621])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_287,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_298,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_287])).

tff(c_367,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_382,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_367])).

tff(c_58,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_299,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_287])).

tff(c_379,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_367])).

tff(c_428,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_379])).

tff(c_636,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_428])).

tff(c_2157,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2144,c_636])).

tff(c_2159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:12:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.67  
% 3.58/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.58/1.67  
% 3.58/1.67  %Foreground sorts:
% 3.58/1.67  
% 3.58/1.67  
% 3.58/1.67  %Background operators:
% 3.58/1.67  
% 3.58/1.67  
% 3.58/1.67  %Foreground operators:
% 3.58/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.58/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.58/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.67  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.58/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.58/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.58/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.58/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.58/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.67  
% 3.58/1.68  tff(f_97, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.58/1.68  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.58/1.68  tff(f_57, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.58/1.68  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.58/1.68  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.58/1.68  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.58/1.68  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.58/1.68  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.58/1.68  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.58/1.68  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.58/1.68  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.58/1.68  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.58/1.68  tff(c_56, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.58/1.68  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.58/1.68  tff(c_1042, plain, (![A_98, B_99]: (k4_xboole_0(A_98, B_99)=k3_subset_1(A_98, B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.58/1.68  tff(c_1055, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_1042])).
% 3.58/1.68  tff(c_24, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.58/1.68  tff(c_743, plain, (![A_85, C_86, B_87]: (r1_xboole_0(A_85, C_86) | ~r1_xboole_0(B_87, C_86) | ~r1_tarski(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.58/1.68  tff(c_1531, plain, (![A_116, B_117, A_118]: (r1_xboole_0(A_116, B_117) | ~r1_tarski(A_116, k4_xboole_0(A_118, B_117)))), inference(resolution, [status(thm)], [c_24, c_743])).
% 3.58/1.68  tff(c_2012, plain, (![A_129]: (r1_xboole_0(A_129, '#skF_5') | ~r1_tarski(A_129, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_1531])).
% 3.58/1.68  tff(c_2025, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_2012])).
% 3.58/1.68  tff(c_26, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.58/1.68  tff(c_2144, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_2025, c_26])).
% 3.58/1.68  tff(c_16, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.58/1.68  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.58/1.68  tff(c_566, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.58/1.68  tff(c_621, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_566])).
% 3.58/1.68  tff(c_631, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_621])).
% 3.58/1.68  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.58/1.68  tff(c_287, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.58/1.68  tff(c_298, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_287])).
% 3.58/1.68  tff(c_367, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.58/1.68  tff(c_382, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_298, c_367])).
% 3.58/1.68  tff(c_58, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.58/1.68  tff(c_299, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_58, c_287])).
% 3.58/1.68  tff(c_379, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_299, c_367])).
% 3.58/1.68  tff(c_428, plain, (k4_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_379])).
% 3.58/1.68  tff(c_636, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_631, c_428])).
% 3.58/1.68  tff(c_2157, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2144, c_636])).
% 3.58/1.68  tff(c_2159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2157])).
% 3.58/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.68  
% 3.58/1.68  Inference rules
% 3.58/1.68  ----------------------
% 3.58/1.68  #Ref     : 0
% 3.58/1.68  #Sup     : 536
% 3.58/1.68  #Fact    : 0
% 3.58/1.68  #Define  : 0
% 3.58/1.68  #Split   : 3
% 3.58/1.68  #Chain   : 0
% 3.58/1.68  #Close   : 0
% 3.58/1.69  
% 3.58/1.69  Ordering : KBO
% 3.58/1.69  
% 3.58/1.69  Simplification rules
% 3.58/1.69  ----------------------
% 3.58/1.69  #Subsume      : 13
% 3.58/1.69  #Demod        : 437
% 3.58/1.69  #Tautology    : 385
% 3.58/1.69  #SimpNegUnit  : 3
% 3.58/1.69  #BackRed      : 11
% 3.58/1.69  
% 3.58/1.69  #Partial instantiations: 0
% 3.58/1.69  #Strategies tried      : 1
% 3.58/1.69  
% 3.58/1.69  Timing (in seconds)
% 3.58/1.69  ----------------------
% 3.80/1.69  Preprocessing        : 0.34
% 3.80/1.69  Parsing              : 0.18
% 3.80/1.69  CNF conversion       : 0.03
% 3.80/1.69  Main loop            : 0.52
% 3.80/1.69  Inferencing          : 0.17
% 3.80/1.69  Reduction            : 0.21
% 3.80/1.69  Demodulation         : 0.16
% 3.80/1.69  BG Simplification    : 0.02
% 3.80/1.69  Subsumption          : 0.09
% 3.80/1.69  Abstraction          : 0.02
% 3.80/1.69  MUC search           : 0.00
% 3.80/1.69  Cooper               : 0.00
% 3.80/1.69  Total                : 0.89
% 3.80/1.69  Index Insertion      : 0.00
% 3.80/1.69  Index Deletion       : 0.00
% 3.80/1.69  Index Matching       : 0.00
% 3.80/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
