%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:31 EST 2020

% Result     : Theorem 5.68s
% Output     : CNFRefutation 5.68s
% Verified   : 
% Statistics : Number of formulae       :   63 (  71 expanded)
%              Number of leaves         :   38 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 (  92 expanded)
%              Number of equality atoms :   33 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
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

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_52,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_159,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_147])).

tff(c_162,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_159])).

tff(c_172,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_172])).

tff(c_190,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_187])).

tff(c_42,plain,(
    ! [B_42] : k4_xboole_0(k1_tarski(B_42),k1_tarski(B_42)) != k1_tarski(B_42) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_191,plain,(
    ! [B_42] : k1_tarski(B_42) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_42])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_58,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_54,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6539,plain,(
    ! [D_29503,C_29504,B_29505,A_29506] :
      ( r2_hidden(k1_funct_1(D_29503,C_29504),B_29505)
      | k1_xboole_0 = B_29505
      | ~ r2_hidden(C_29504,A_29506)
      | ~ m1_subset_1(D_29503,k1_zfmisc_1(k2_zfmisc_1(A_29506,B_29505)))
      | ~ v1_funct_2(D_29503,A_29506,B_29505)
      | ~ v1_funct_1(D_29503) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6740,plain,(
    ! [D_30644,B_30645] :
      ( r2_hidden(k1_funct_1(D_30644,'#skF_5'),B_30645)
      | k1_xboole_0 = B_30645
      | ~ m1_subset_1(D_30644,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_30645)))
      | ~ v1_funct_2(D_30644,'#skF_3',B_30645)
      | ~ v1_funct_1(D_30644) ) ),
    inference(resolution,[status(thm)],[c_54,c_6539])).

tff(c_6757,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_6740])).

tff(c_6760,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_6757])).

tff(c_6761,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_6760])).

tff(c_28,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_285,plain,(
    ! [D_77,B_78,A_79] :
      ( D_77 = B_78
      | D_77 = A_79
      | ~ r2_hidden(D_77,k2_tarski(A_79,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_288,plain,(
    ! [D_77,A_13] :
      ( D_77 = A_13
      | D_77 = A_13
      | ~ r2_hidden(D_77,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_285])).

tff(c_6766,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6761,c_288])).

tff(c_6827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_6766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:46:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.68/2.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.68/2.09  
% 5.68/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.68/2.09  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.68/2.09  
% 5.68/2.09  %Foreground sorts:
% 5.68/2.09  
% 5.68/2.09  
% 5.68/2.09  %Background operators:
% 5.68/2.09  
% 5.68/2.09  
% 5.68/2.09  %Foreground operators:
% 5.68/2.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.68/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.68/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.68/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.68/2.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.68/2.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.68/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.68/2.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.68/2.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.68/2.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.68/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.68/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.68/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.68/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.68/2.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.68/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.68/2.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.68/2.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.68/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.68/2.09  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.68/2.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.68/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.68/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.68/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.68/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.68/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.68/2.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.68/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.68/2.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.68/2.09  
% 5.68/2.10  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 5.68/2.10  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.68/2.10  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.68/2.10  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.68/2.10  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.68/2.10  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 5.68/2.10  tff(f_77, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 5.68/2.10  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.68/2.10  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.68/2.10  tff(c_52, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.68/2.10  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.68/2.10  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.68/2.10  tff(c_147, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.68/2.10  tff(c_159, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_147])).
% 5.68/2.10  tff(c_162, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_159])).
% 5.68/2.10  tff(c_172, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.68/2.10  tff(c_187, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_162, c_172])).
% 5.68/2.10  tff(c_190, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_187])).
% 5.68/2.10  tff(c_42, plain, (![B_42]: (k4_xboole_0(k1_tarski(B_42), k1_tarski(B_42))!=k1_tarski(B_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.68/2.10  tff(c_191, plain, (![B_42]: (k1_tarski(B_42)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_42])).
% 5.68/2.10  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.68/2.10  tff(c_58, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.68/2.10  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.68/2.10  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.68/2.10  tff(c_6539, plain, (![D_29503, C_29504, B_29505, A_29506]: (r2_hidden(k1_funct_1(D_29503, C_29504), B_29505) | k1_xboole_0=B_29505 | ~r2_hidden(C_29504, A_29506) | ~m1_subset_1(D_29503, k1_zfmisc_1(k2_zfmisc_1(A_29506, B_29505))) | ~v1_funct_2(D_29503, A_29506, B_29505) | ~v1_funct_1(D_29503))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.68/2.10  tff(c_6740, plain, (![D_30644, B_30645]: (r2_hidden(k1_funct_1(D_30644, '#skF_5'), B_30645) | k1_xboole_0=B_30645 | ~m1_subset_1(D_30644, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_30645))) | ~v1_funct_2(D_30644, '#skF_3', B_30645) | ~v1_funct_1(D_30644))), inference(resolution, [status(thm)], [c_54, c_6539])).
% 5.68/2.10  tff(c_6757, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_6740])).
% 5.68/2.10  tff(c_6760, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_6757])).
% 5.68/2.10  tff(c_6761, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_191, c_6760])).
% 5.68/2.10  tff(c_28, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.68/2.10  tff(c_285, plain, (![D_77, B_78, A_79]: (D_77=B_78 | D_77=A_79 | ~r2_hidden(D_77, k2_tarski(A_79, B_78)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.68/2.10  tff(c_288, plain, (![D_77, A_13]: (D_77=A_13 | D_77=A_13 | ~r2_hidden(D_77, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_285])).
% 5.68/2.10  tff(c_6766, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_6761, c_288])).
% 5.68/2.10  tff(c_6827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_6766])).
% 5.68/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.68/2.10  
% 5.68/2.10  Inference rules
% 5.68/2.10  ----------------------
% 5.68/2.10  #Ref     : 0
% 5.68/2.10  #Sup     : 706
% 5.68/2.10  #Fact    : 8
% 5.68/2.10  #Define  : 0
% 5.68/2.10  #Split   : 5
% 5.68/2.10  #Chain   : 0
% 5.68/2.10  #Close   : 0
% 5.68/2.10  
% 5.68/2.10  Ordering : KBO
% 5.68/2.10  
% 5.68/2.10  Simplification rules
% 5.68/2.10  ----------------------
% 5.68/2.10  #Subsume      : 83
% 5.68/2.10  #Demod        : 323
% 5.68/2.10  #Tautology    : 246
% 5.68/2.10  #SimpNegUnit  : 31
% 5.68/2.10  #BackRed      : 1
% 5.68/2.10  
% 5.68/2.10  #Partial instantiations: 7682
% 5.68/2.10  #Strategies tried      : 1
% 5.68/2.10  
% 5.68/2.10  Timing (in seconds)
% 5.68/2.10  ----------------------
% 5.68/2.10  Preprocessing        : 0.34
% 5.68/2.10  Parsing              : 0.19
% 5.68/2.10  CNF conversion       : 0.02
% 5.68/2.10  Main loop            : 0.98
% 5.68/2.10  Inferencing          : 0.57
% 5.68/2.10  Reduction            : 0.23
% 5.68/2.10  Demodulation         : 0.17
% 5.68/2.10  BG Simplification    : 0.04
% 5.68/2.10  Subsumption          : 0.10
% 5.68/2.10  Abstraction          : 0.05
% 5.68/2.10  MUC search           : 0.00
% 5.68/2.10  Cooper               : 0.00
% 5.68/2.10  Total                : 1.35
% 5.68/2.10  Index Insertion      : 0.00
% 5.68/2.10  Index Deletion       : 0.00
% 5.68/2.10  Index Matching       : 0.00
% 5.68/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
