%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:29 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   60 (  72 expanded)
%              Number of leaves         :   37 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 115 expanded)
%              Number of equality atoms :   42 (  54 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_60,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [A_65,B_66] : k4_xboole_0(k1_tarski(A_65),k2_tarski(A_65,B_66)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,(
    ! [A_3] : k4_xboole_0(k1_tarski(A_3),k1_tarski(A_3)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_118])).

tff(c_20,plain,(
    ! [B_34] : k4_xboole_0(k1_tarski(B_34),k1_tarski(B_34)) != k1_tarski(B_34) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_137,plain,(
    ! [B_34] : k1_tarski(B_34) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_20])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_390,plain,(
    ! [D_160,C_161,B_162,A_163] :
      ( r2_hidden(k1_funct_1(D_160,C_161),B_162)
      | k1_xboole_0 = B_162
      | ~ r2_hidden(C_161,A_163)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162)))
      | ~ v1_funct_2(D_160,A_163,B_162)
      | ~ v1_funct_1(D_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_424,plain,(
    ! [D_164,B_165] :
      ( r2_hidden(k1_funct_1(D_164,'#skF_5'),B_165)
      | k1_xboole_0 = B_165
      | ~ m1_subset_1(D_164,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_165)))
      | ~ v1_funct_2(D_164,'#skF_3',B_165)
      | ~ v1_funct_1(D_164) ) ),
    inference(resolution,[status(thm)],[c_62,c_390])).

tff(c_427,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_424])).

tff(c_430,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_427])).

tff(c_431,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_430])).

tff(c_6,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_305,plain,(
    ! [A_113,F_117,D_115,B_114,C_116] :
      ( F_117 = D_115
      | F_117 = C_116
      | F_117 = B_114
      | F_117 = A_113
      | ~ r2_hidden(F_117,k2_enumset1(A_113,B_114,C_116,D_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_329,plain,(
    ! [F_118,C_119,B_120,A_121] :
      ( F_118 = C_119
      | F_118 = B_120
      | F_118 = A_121
      | F_118 = A_121
      | ~ r2_hidden(F_118,k1_enumset1(A_121,B_120,C_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_305])).

tff(c_348,plain,(
    ! [F_122,B_123,A_124] :
      ( F_122 = B_123
      | F_122 = A_124
      | F_122 = A_124
      | F_122 = A_124
      | ~ r2_hidden(F_122,k2_tarski(A_124,B_123)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_329])).

tff(c_357,plain,(
    ! [F_122,A_3] :
      ( F_122 = A_3
      | F_122 = A_3
      | F_122 = A_3
      | F_122 = A_3
      | ~ r2_hidden(F_122,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_348])).

tff(c_436,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_431,c_357])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_60,c_60,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:19:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.37  
% 2.74/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.37  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.74/1.37  
% 2.74/1.37  %Foreground sorts:
% 2.74/1.37  
% 2.74/1.37  
% 2.74/1.37  %Background operators:
% 2.74/1.37  
% 2.74/1.37  
% 2.74/1.37  %Foreground operators:
% 2.74/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.74/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.74/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.74/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.74/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.74/1.37  
% 2.74/1.38  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.74/1.38  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.74/1.38  tff(f_50, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.74/1.38  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.74/1.38  tff(f_82, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.74/1.38  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.74/1.38  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.74/1.38  tff(f_68, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.74/1.38  tff(c_60, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.38  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.74/1.38  tff(c_118, plain, (![A_65, B_66]: (k4_xboole_0(k1_tarski(A_65), k2_tarski(A_65, B_66))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.74/1.38  tff(c_125, plain, (![A_3]: (k4_xboole_0(k1_tarski(A_3), k1_tarski(A_3))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_118])).
% 2.74/1.38  tff(c_20, plain, (![B_34]: (k4_xboole_0(k1_tarski(B_34), k1_tarski(B_34))!=k1_tarski(B_34))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.74/1.38  tff(c_137, plain, (![B_34]: (k1_tarski(B_34)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_20])).
% 2.74/1.38  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.38  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.38  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.38  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.38  tff(c_390, plain, (![D_160, C_161, B_162, A_163]: (r2_hidden(k1_funct_1(D_160, C_161), B_162) | k1_xboole_0=B_162 | ~r2_hidden(C_161, A_163) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))) | ~v1_funct_2(D_160, A_163, B_162) | ~v1_funct_1(D_160))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.74/1.38  tff(c_424, plain, (![D_164, B_165]: (r2_hidden(k1_funct_1(D_164, '#skF_5'), B_165) | k1_xboole_0=B_165 | ~m1_subset_1(D_164, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_165))) | ~v1_funct_2(D_164, '#skF_3', B_165) | ~v1_funct_1(D_164))), inference(resolution, [status(thm)], [c_62, c_390])).
% 2.74/1.38  tff(c_427, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_424])).
% 2.74/1.38  tff(c_430, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_427])).
% 2.74/1.38  tff(c_431, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_137, c_430])).
% 2.74/1.38  tff(c_6, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.38  tff(c_8, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.38  tff(c_305, plain, (![A_113, F_117, D_115, B_114, C_116]: (F_117=D_115 | F_117=C_116 | F_117=B_114 | F_117=A_113 | ~r2_hidden(F_117, k2_enumset1(A_113, B_114, C_116, D_115)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.74/1.38  tff(c_329, plain, (![F_118, C_119, B_120, A_121]: (F_118=C_119 | F_118=B_120 | F_118=A_121 | F_118=A_121 | ~r2_hidden(F_118, k1_enumset1(A_121, B_120, C_119)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_305])).
% 2.74/1.38  tff(c_348, plain, (![F_122, B_123, A_124]: (F_122=B_123 | F_122=A_124 | F_122=A_124 | F_122=A_124 | ~r2_hidden(F_122, k2_tarski(A_124, B_123)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_329])).
% 2.74/1.38  tff(c_357, plain, (![F_122, A_3]: (F_122=A_3 | F_122=A_3 | F_122=A_3 | F_122=A_3 | ~r2_hidden(F_122, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_348])).
% 2.74/1.38  tff(c_436, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_431, c_357])).
% 2.74/1.38  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_60, c_60, c_436])).
% 2.74/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.38  
% 2.74/1.38  Inference rules
% 2.74/1.38  ----------------------
% 2.74/1.38  #Ref     : 0
% 2.74/1.38  #Sup     : 86
% 2.74/1.38  #Fact    : 0
% 2.74/1.38  #Define  : 0
% 2.74/1.38  #Split   : 0
% 2.74/1.38  #Chain   : 0
% 2.74/1.38  #Close   : 0
% 2.74/1.38  
% 2.74/1.38  Ordering : KBO
% 2.74/1.38  
% 2.74/1.38  Simplification rules
% 2.74/1.38  ----------------------
% 2.74/1.38  #Subsume      : 0
% 2.74/1.38  #Demod        : 13
% 2.74/1.38  #Tautology    : 57
% 2.74/1.38  #SimpNegUnit  : 4
% 2.74/1.38  #BackRed      : 0
% 2.74/1.38  
% 2.74/1.38  #Partial instantiations: 0
% 2.74/1.38  #Strategies tried      : 1
% 2.74/1.38  
% 2.74/1.38  Timing (in seconds)
% 2.74/1.38  ----------------------
% 2.74/1.39  Preprocessing        : 0.35
% 2.74/1.39  Parsing              : 0.17
% 2.74/1.39  CNF conversion       : 0.03
% 2.74/1.39  Main loop            : 0.28
% 2.74/1.39  Inferencing          : 0.10
% 2.74/1.39  Reduction            : 0.09
% 2.74/1.39  Demodulation         : 0.06
% 2.74/1.39  BG Simplification    : 0.02
% 2.74/1.39  Subsumption          : 0.05
% 2.74/1.39  Abstraction          : 0.02
% 2.74/1.39  MUC search           : 0.00
% 2.74/1.39  Cooper               : 0.00
% 2.74/1.39  Total                : 0.66
% 2.74/1.39  Index Insertion      : 0.00
% 2.74/1.39  Index Deletion       : 0.00
% 2.74/1.39  Index Matching       : 0.00
% 2.74/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
