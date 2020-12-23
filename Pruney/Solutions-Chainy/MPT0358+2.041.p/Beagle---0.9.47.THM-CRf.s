%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:05 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 116 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 179 expanded)
%              Number of equality atoms :   29 (  56 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_66,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_62,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    ! [B_12] : k3_xboole_0(B_12,B_12) = B_12 ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_109,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_121,plain,(
    ! [B_41] : k5_xboole_0(B_41,B_41) = k4_xboole_0(B_41,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_109])).

tff(c_28,plain,(
    ! [A_20] : k1_subset_1(A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_41,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_34])).

tff(c_76,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_40,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_40])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_42])).

tff(c_24,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_78,plain,(
    ! [A_17] : k5_xboole_0(A_17,'#skF_4') = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_24])).

tff(c_128,plain,(
    k4_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_78])).

tff(c_26,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_141,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_26])).

tff(c_164,plain,(
    ! [A_49,B_50,C_51] :
      ( ~ r1_xboole_0(A_49,B_50)
      | ~ r2_hidden(C_51,B_50)
      | ~ r2_hidden(C_51,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_171,plain,(
    ! [C_52] : ~ r2_hidden(C_52,'#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_164])).

tff(c_186,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_171])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_76])).

tff(c_204,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_205,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_327,plain,(
    ! [C_76,B_77,A_78] :
      ( r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_516,plain,(
    ! [A_100,B_101,B_102] :
      ( r2_hidden('#skF_1'(A_100,B_101),B_102)
      | ~ r1_tarski(A_100,B_102)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_327])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_425,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_429,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_425])).

tff(c_288,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,B_71)
      | ~ r2_hidden(C_72,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_297,plain,(
    ! [C_72,B_19,A_18] :
      ( ~ r2_hidden(C_72,B_19)
      | ~ r2_hidden(C_72,k4_xboole_0(A_18,B_19)) ) ),
    inference(resolution,[status(thm)],[c_26,c_288])).

tff(c_433,plain,(
    ! [C_72] :
      ( ~ r2_hidden(C_72,'#skF_4')
      | ~ r2_hidden(C_72,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_297])).

tff(c_920,plain,(
    ! [A_157,B_158] :
      ( ~ r2_hidden('#skF_1'(A_157,B_158),'#skF_4')
      | ~ r1_tarski(A_157,k3_subset_1('#skF_3','#skF_4'))
      | r1_tarski(A_157,B_158) ) ),
    inference(resolution,[status(thm)],[c_516,c_433])).

tff(c_928,plain,(
    ! [B_2] :
      ( ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
      | r1_tarski('#skF_4',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_920])).

tff(c_934,plain,(
    ! [B_159] : r1_tarski('#skF_4',B_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_928])).

tff(c_222,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_237,plain,(
    ! [B_65] : k5_xboole_0(B_65,B_65) = k4_xboole_0(B_65,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_222])).

tff(c_244,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_24])).

tff(c_257,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_26])).

tff(c_298,plain,(
    ! [C_73] : ~ r2_hidden(C_73,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_257,c_288])).

tff(c_314,plain,(
    ! [B_74] : r1_tarski(k1_xboole_0,B_74) ),
    inference(resolution,[status(thm)],[c_6,c_298])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_320,plain,(
    ! [B_74] :
      ( k1_xboole_0 = B_74
      | ~ r1_tarski(B_74,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_314,c_14])).

tff(c_941,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_934,c_320])).

tff(c_952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.49  
% 2.99/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.99/1.50  
% 2.99/1.50  %Foreground sorts:
% 2.99/1.50  
% 2.99/1.50  
% 2.99/1.50  %Background operators:
% 2.99/1.50  
% 2.99/1.50  
% 2.99/1.50  %Foreground operators:
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.99/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.50  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.99/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.99/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.50  
% 2.99/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.99/1.51  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.99/1.51  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.99/1.51  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.99/1.51  tff(f_68, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.99/1.51  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.99/1.51  tff(f_64, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.99/1.51  tff(f_66, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.99/1.51  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.99/1.51  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.99/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.51  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.51  tff(c_62, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.51  tff(c_66, plain, (![B_12]: (k3_xboole_0(B_12, B_12)=B_12)), inference(resolution, [status(thm)], [c_18, c_62])).
% 2.99/1.51  tff(c_109, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.51  tff(c_121, plain, (![B_41]: (k5_xboole_0(B_41, B_41)=k4_xboole_0(B_41, B_41))), inference(superposition, [status(thm), theory('equality')], [c_66, c_109])).
% 2.99/1.51  tff(c_28, plain, (![A_20]: (k1_subset_1(A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.99/1.51  tff(c_34, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.99/1.51  tff(c_41, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_34])).
% 2.99/1.51  tff(c_76, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_41])).
% 2.99/1.51  tff(c_40, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.99/1.51  tff(c_42, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_40])).
% 2.99/1.51  tff(c_77, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_76, c_42])).
% 2.99/1.51  tff(c_24, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.99/1.51  tff(c_78, plain, (![A_17]: (k5_xboole_0(A_17, '#skF_4')=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_24])).
% 2.99/1.51  tff(c_128, plain, (k4_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_121, c_78])).
% 2.99/1.51  tff(c_26, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.99/1.51  tff(c_141, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_128, c_26])).
% 2.99/1.51  tff(c_164, plain, (![A_49, B_50, C_51]: (~r1_xboole_0(A_49, B_50) | ~r2_hidden(C_51, B_50) | ~r2_hidden(C_51, A_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.99/1.51  tff(c_171, plain, (![C_52]: (~r2_hidden(C_52, '#skF_4'))), inference(resolution, [status(thm)], [c_141, c_164])).
% 2.99/1.51  tff(c_186, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_171])).
% 2.99/1.51  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_76])).
% 2.99/1.51  tff(c_204, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_41])).
% 2.99/1.51  tff(c_205, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_41])).
% 2.99/1.51  tff(c_327, plain, (![C_76, B_77, A_78]: (r2_hidden(C_76, B_77) | ~r2_hidden(C_76, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.51  tff(c_516, plain, (![A_100, B_101, B_102]: (r2_hidden('#skF_1'(A_100, B_101), B_102) | ~r1_tarski(A_100, B_102) | r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_6, c_327])).
% 2.99/1.51  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.99/1.51  tff(c_425, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.99/1.51  tff(c_429, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_425])).
% 2.99/1.51  tff(c_288, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, B_71) | ~r2_hidden(C_72, A_70))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.99/1.51  tff(c_297, plain, (![C_72, B_19, A_18]: (~r2_hidden(C_72, B_19) | ~r2_hidden(C_72, k4_xboole_0(A_18, B_19)))), inference(resolution, [status(thm)], [c_26, c_288])).
% 2.99/1.51  tff(c_433, plain, (![C_72]: (~r2_hidden(C_72, '#skF_4') | ~r2_hidden(C_72, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_429, c_297])).
% 2.99/1.51  tff(c_920, plain, (![A_157, B_158]: (~r2_hidden('#skF_1'(A_157, B_158), '#skF_4') | ~r1_tarski(A_157, k3_subset_1('#skF_3', '#skF_4')) | r1_tarski(A_157, B_158))), inference(resolution, [status(thm)], [c_516, c_433])).
% 2.99/1.51  tff(c_928, plain, (![B_2]: (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_920])).
% 2.99/1.51  tff(c_934, plain, (![B_159]: (r1_tarski('#skF_4', B_159))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_928])).
% 2.99/1.51  tff(c_222, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.51  tff(c_237, plain, (![B_65]: (k5_xboole_0(B_65, B_65)=k4_xboole_0(B_65, B_65))), inference(superposition, [status(thm), theory('equality')], [c_66, c_222])).
% 2.99/1.51  tff(c_244, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_237, c_24])).
% 2.99/1.51  tff(c_257, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_244, c_26])).
% 2.99/1.51  tff(c_298, plain, (![C_73]: (~r2_hidden(C_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_257, c_288])).
% 2.99/1.51  tff(c_314, plain, (![B_74]: (r1_tarski(k1_xboole_0, B_74))), inference(resolution, [status(thm)], [c_6, c_298])).
% 2.99/1.51  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.51  tff(c_320, plain, (![B_74]: (k1_xboole_0=B_74 | ~r1_tarski(B_74, k1_xboole_0))), inference(resolution, [status(thm)], [c_314, c_14])).
% 2.99/1.51  tff(c_941, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_934, c_320])).
% 2.99/1.51  tff(c_952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_941])).
% 2.99/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.51  
% 2.99/1.51  Inference rules
% 2.99/1.51  ----------------------
% 2.99/1.51  #Ref     : 0
% 2.99/1.51  #Sup     : 214
% 2.99/1.51  #Fact    : 0
% 2.99/1.51  #Define  : 0
% 2.99/1.51  #Split   : 3
% 2.99/1.51  #Chain   : 0
% 2.99/1.51  #Close   : 0
% 2.99/1.51  
% 2.99/1.51  Ordering : KBO
% 2.99/1.51  
% 2.99/1.51  Simplification rules
% 2.99/1.51  ----------------------
% 2.99/1.51  #Subsume      : 32
% 2.99/1.51  #Demod        : 57
% 2.99/1.51  #Tautology    : 69
% 2.99/1.51  #SimpNegUnit  : 3
% 2.99/1.51  #BackRed      : 3
% 2.99/1.51  
% 2.99/1.51  #Partial instantiations: 0
% 2.99/1.51  #Strategies tried      : 1
% 2.99/1.51  
% 2.99/1.51  Timing (in seconds)
% 2.99/1.51  ----------------------
% 2.99/1.52  Preprocessing        : 0.32
% 2.99/1.52  Parsing              : 0.18
% 2.99/1.52  CNF conversion       : 0.02
% 2.99/1.52  Main loop            : 0.39
% 2.99/1.52  Inferencing          : 0.15
% 2.99/1.52  Reduction            : 0.11
% 2.99/1.52  Demodulation         : 0.08
% 2.99/1.52  BG Simplification    : 0.02
% 2.99/1.52  Subsumption          : 0.08
% 2.99/1.52  Abstraction          : 0.02
% 2.99/1.52  MUC search           : 0.00
% 2.99/1.52  Cooper               : 0.00
% 2.99/1.52  Total                : 0.74
% 2.99/1.52  Index Insertion      : 0.00
% 2.99/1.52  Index Deletion       : 0.00
% 2.99/1.52  Index Matching       : 0.00
% 2.99/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
