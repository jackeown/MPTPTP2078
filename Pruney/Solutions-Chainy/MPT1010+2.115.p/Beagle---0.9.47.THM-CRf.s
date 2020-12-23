%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:20 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   59 (  63 expanded)
%              Number of leaves         :   37 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 (  80 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_46,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_104,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_104])).

tff(c_116,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_113])).

tff(c_40,plain,(
    ! [B_42] : k4_xboole_0(k1_tarski(B_42),k1_tarski(B_42)) != k1_tarski(B_42) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_124,plain,(
    ! [B_42] : k1_tarski(B_42) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_40])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_238,plain,(
    ! [D_104,C_105,B_106,A_107] :
      ( r2_hidden(k1_funct_1(D_104,C_105),B_106)
      | k1_xboole_0 = B_106
      | ~ r2_hidden(C_105,A_107)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106)))
      | ~ v1_funct_2(D_104,A_107,B_106)
      | ~ v1_funct_1(D_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_251,plain,(
    ! [D_108,B_109] :
      ( r2_hidden(k1_funct_1(D_108,'#skF_5'),B_109)
      | k1_xboole_0 = B_109
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_109)))
      | ~ v1_funct_2(D_108,'#skF_3',B_109)
      | ~ v1_funct_1(D_108) ) ),
    inference(resolution,[status(thm)],[c_48,c_238])).

tff(c_254,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_251])).

tff(c_257,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_254])).

tff(c_258,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_257])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_263,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_258,c_14])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.33  
% 2.36/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.34  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.36/1.34  
% 2.36/1.34  %Foreground sorts:
% 2.36/1.34  
% 2.36/1.34  
% 2.36/1.34  %Background operators:
% 2.36/1.34  
% 2.36/1.34  
% 2.36/1.34  %Foreground operators:
% 2.36/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.34  
% 2.36/1.35  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.36/1.35  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.36/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.36/1.35  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.36/1.35  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.36/1.35  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.36/1.35  tff(f_77, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.36/1.35  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.36/1.35  tff(c_46, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.36/1.35  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.36/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.35  tff(c_90, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.35  tff(c_94, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_90])).
% 2.36/1.35  tff(c_104, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.35  tff(c_113, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_94, c_104])).
% 2.36/1.35  tff(c_116, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_113])).
% 2.36/1.35  tff(c_40, plain, (![B_42]: (k4_xboole_0(k1_tarski(B_42), k1_tarski(B_42))!=k1_tarski(B_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.36/1.35  tff(c_124, plain, (![B_42]: (k1_tarski(B_42)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_116, c_40])).
% 2.36/1.35  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.36/1.35  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.36/1.35  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.36/1.35  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.36/1.35  tff(c_238, plain, (![D_104, C_105, B_106, A_107]: (r2_hidden(k1_funct_1(D_104, C_105), B_106) | k1_xboole_0=B_106 | ~r2_hidden(C_105, A_107) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))) | ~v1_funct_2(D_104, A_107, B_106) | ~v1_funct_1(D_104))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.36/1.35  tff(c_251, plain, (![D_108, B_109]: (r2_hidden(k1_funct_1(D_108, '#skF_5'), B_109) | k1_xboole_0=B_109 | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_109))) | ~v1_funct_2(D_108, '#skF_3', B_109) | ~v1_funct_1(D_108))), inference(resolution, [status(thm)], [c_48, c_238])).
% 2.36/1.35  tff(c_254, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_251])).
% 2.36/1.35  tff(c_257, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_254])).
% 2.36/1.35  tff(c_258, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_124, c_257])).
% 2.36/1.35  tff(c_14, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.35  tff(c_263, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_258, c_14])).
% 2.36/1.35  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_263])).
% 2.36/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  Inference rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Ref     : 0
% 2.36/1.35  #Sup     : 44
% 2.36/1.35  #Fact    : 0
% 2.36/1.35  #Define  : 0
% 2.36/1.35  #Split   : 0
% 2.36/1.35  #Chain   : 0
% 2.36/1.35  #Close   : 0
% 2.36/1.35  
% 2.36/1.35  Ordering : KBO
% 2.36/1.35  
% 2.36/1.35  Simplification rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Subsume      : 0
% 2.36/1.35  #Demod        : 8
% 2.36/1.35  #Tautology    : 34
% 2.36/1.35  #SimpNegUnit  : 4
% 2.36/1.35  #BackRed      : 1
% 2.36/1.35  
% 2.36/1.35  #Partial instantiations: 0
% 2.36/1.35  #Strategies tried      : 1
% 2.36/1.35  
% 2.36/1.35  Timing (in seconds)
% 2.36/1.35  ----------------------
% 2.36/1.35  Preprocessing        : 0.36
% 2.36/1.35  Parsing              : 0.19
% 2.36/1.35  CNF conversion       : 0.03
% 2.36/1.35  Main loop            : 0.19
% 2.36/1.35  Inferencing          : 0.07
% 2.36/1.35  Reduction            : 0.06
% 2.36/1.35  Demodulation         : 0.04
% 2.36/1.35  BG Simplification    : 0.02
% 2.36/1.35  Subsumption          : 0.03
% 2.36/1.35  Abstraction          : 0.02
% 2.36/1.35  MUC search           : 0.00
% 2.36/1.35  Cooper               : 0.00
% 2.36/1.35  Total                : 0.58
% 2.36/1.35  Index Insertion      : 0.00
% 2.36/1.35  Index Deletion       : 0.00
% 2.36/1.35  Index Matching       : 0.00
% 2.36/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
