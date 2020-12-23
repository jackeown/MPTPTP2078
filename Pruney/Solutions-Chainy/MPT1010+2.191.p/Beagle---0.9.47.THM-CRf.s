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
% DateTime   : Thu Dec  3 10:15:30 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 112 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_36,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [D_23,B_24] : r2_hidden(D_23,k2_tarski(D_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,(
    ! [A_11] : r2_hidden(A_11,k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_62])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(k1_tarski(A_12),B_13) = k1_tarski(A_12)
      | r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden(A_37,B_38)
      | k4_xboole_0(k1_tarski(A_37),B_38) != k1_tarski(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_207,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden(A_49,k4_xboole_0(k1_tarski(A_49),B_50))
      | k3_xboole_0(k1_tarski(A_49),B_50) != k1_tarski(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_113])).

tff(c_214,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden(A_12,k1_tarski(A_12))
      | k3_xboole_0(k1_tarski(A_12),B_13) != k1_tarski(A_12)
      | r2_hidden(A_12,B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_207])).

tff(c_222,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(k1_tarski(A_54),B_55) != k1_tarski(A_54)
      | r2_hidden(A_54,B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_214])).

tff(c_231,plain,(
    ! [A_56] :
      ( k1_tarski(A_56) != k1_xboole_0
      | r2_hidden(A_56,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_222])).

tff(c_32,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_238,plain,(
    ! [A_56] :
      ( ~ r1_tarski(k1_xboole_0,A_56)
      | k1_tarski(A_56) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_231,c_32])).

tff(c_242,plain,(
    ! [A_56] : k1_tarski(A_56) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_238])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3085,plain,(
    ! [D_3165,C_3166,B_3167,A_3168] :
      ( r2_hidden(k1_funct_1(D_3165,C_3166),B_3167)
      | k1_xboole_0 = B_3167
      | ~ r2_hidden(C_3166,A_3168)
      | ~ m1_subset_1(D_3165,k1_zfmisc_1(k2_zfmisc_1(A_3168,B_3167)))
      | ~ v1_funct_2(D_3165,A_3168,B_3167)
      | ~ v1_funct_1(D_3165) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5908,plain,(
    ! [D_4884,B_4885] :
      ( r2_hidden(k1_funct_1(D_4884,'#skF_5'),B_4885)
      | k1_xboole_0 = B_4885
      | ~ m1_subset_1(D_4884,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_4885)))
      | ~ v1_funct_2(D_4884,'#skF_3',B_4885)
      | ~ v1_funct_1(D_4884) ) ),
    inference(resolution,[status(thm)],[c_38,c_3085])).

tff(c_5917,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_5908])).

tff(c_5920,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_5917])).

tff(c_5921,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_5920])).

tff(c_118,plain,(
    ! [D_39,B_40,A_41] :
      ( D_39 = B_40
      | D_39 = A_41
      | ~ r2_hidden(D_39,k2_tarski(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [D_39,A_11] :
      ( D_39 = A_11
      | D_39 = A_11
      | ~ r2_hidden(D_39,k1_tarski(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_118])).

tff(c_5926,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5921,c_127])).

tff(c_5973,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_5926])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.95  
% 5.00/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.95  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.00/1.95  
% 5.00/1.95  %Foreground sorts:
% 5.00/1.95  
% 5.00/1.95  
% 5.00/1.95  %Background operators:
% 5.00/1.95  
% 5.00/1.95  
% 5.00/1.95  %Foreground operators:
% 5.00/1.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.00/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.00/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.00/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.00/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.00/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.00/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.00/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.00/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.00/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.00/1.95  tff('#skF_6', type, '#skF_6': $i).
% 5.00/1.95  tff('#skF_3', type, '#skF_3': $i).
% 5.00/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.00/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.00/1.95  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.00/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.00/1.95  tff('#skF_4', type, '#skF_4': $i).
% 5.00/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.00/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.00/1.95  
% 5.00/1.96  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 5.00/1.96  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.00/1.96  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.00/1.96  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.00/1.96  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.00/1.96  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 5.00/1.96  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.00/1.96  tff(f_52, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.00/1.96  tff(f_64, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 5.00/1.96  tff(c_36, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.00/1.96  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.00/1.96  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.00/1.96  tff(c_26, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.00/1.96  tff(c_62, plain, (![D_23, B_24]: (r2_hidden(D_23, k2_tarski(D_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.00/1.96  tff(c_65, plain, (![A_11]: (r2_hidden(A_11, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_62])).
% 5.00/1.96  tff(c_30, plain, (![A_12, B_13]: (k4_xboole_0(k1_tarski(A_12), B_13)=k1_tarski(A_12) | r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.00/1.96  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.00/1.96  tff(c_113, plain, (![A_37, B_38]: (~r2_hidden(A_37, B_38) | k4_xboole_0(k1_tarski(A_37), B_38)!=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.00/1.96  tff(c_207, plain, (![A_49, B_50]: (~r2_hidden(A_49, k4_xboole_0(k1_tarski(A_49), B_50)) | k3_xboole_0(k1_tarski(A_49), B_50)!=k1_tarski(A_49))), inference(superposition, [status(thm), theory('equality')], [c_6, c_113])).
% 5.00/1.96  tff(c_214, plain, (![A_12, B_13]: (~r2_hidden(A_12, k1_tarski(A_12)) | k3_xboole_0(k1_tarski(A_12), B_13)!=k1_tarski(A_12) | r2_hidden(A_12, B_13))), inference(superposition, [status(thm), theory('equality')], [c_30, c_207])).
% 5.00/1.96  tff(c_222, plain, (![A_54, B_55]: (k3_xboole_0(k1_tarski(A_54), B_55)!=k1_tarski(A_54) | r2_hidden(A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_214])).
% 5.00/1.96  tff(c_231, plain, (![A_56]: (k1_tarski(A_56)!=k1_xboole_0 | r2_hidden(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_222])).
% 5.00/1.96  tff(c_32, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.00/1.96  tff(c_238, plain, (![A_56]: (~r1_tarski(k1_xboole_0, A_56) | k1_tarski(A_56)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_231, c_32])).
% 5.00/1.96  tff(c_242, plain, (![A_56]: (k1_tarski(A_56)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_238])).
% 5.00/1.96  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.00/1.96  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.00/1.96  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.00/1.96  tff(c_38, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.00/1.96  tff(c_3085, plain, (![D_3165, C_3166, B_3167, A_3168]: (r2_hidden(k1_funct_1(D_3165, C_3166), B_3167) | k1_xboole_0=B_3167 | ~r2_hidden(C_3166, A_3168) | ~m1_subset_1(D_3165, k1_zfmisc_1(k2_zfmisc_1(A_3168, B_3167))) | ~v1_funct_2(D_3165, A_3168, B_3167) | ~v1_funct_1(D_3165))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.00/1.96  tff(c_5908, plain, (![D_4884, B_4885]: (r2_hidden(k1_funct_1(D_4884, '#skF_5'), B_4885) | k1_xboole_0=B_4885 | ~m1_subset_1(D_4884, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_4885))) | ~v1_funct_2(D_4884, '#skF_3', B_4885) | ~v1_funct_1(D_4884))), inference(resolution, [status(thm)], [c_38, c_3085])).
% 5.00/1.96  tff(c_5917, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_5908])).
% 5.00/1.96  tff(c_5920, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_5917])).
% 5.00/1.96  tff(c_5921, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_242, c_5920])).
% 5.00/1.96  tff(c_118, plain, (![D_39, B_40, A_41]: (D_39=B_40 | D_39=A_41 | ~r2_hidden(D_39, k2_tarski(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.00/1.96  tff(c_127, plain, (![D_39, A_11]: (D_39=A_11 | D_39=A_11 | ~r2_hidden(D_39, k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_118])).
% 5.00/1.96  tff(c_5926, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_5921, c_127])).
% 5.00/1.96  tff(c_5973, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_5926])).
% 5.00/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.96  
% 5.00/1.96  Inference rules
% 5.00/1.96  ----------------------
% 5.00/1.96  #Ref     : 0
% 5.00/1.96  #Sup     : 912
% 5.00/1.96  #Fact    : 8
% 5.00/1.96  #Define  : 0
% 5.00/1.96  #Split   : 5
% 5.00/1.96  #Chain   : 0
% 5.00/1.96  #Close   : 0
% 5.00/1.96  
% 5.00/1.96  Ordering : KBO
% 5.00/1.96  
% 5.00/1.96  Simplification rules
% 5.00/1.96  ----------------------
% 5.00/1.96  #Subsume      : 194
% 5.00/1.96  #Demod        : 251
% 5.00/1.96  #Tautology    : 210
% 5.00/1.96  #SimpNegUnit  : 38
% 5.00/1.96  #BackRed      : 12
% 5.00/1.96  
% 5.00/1.96  #Partial instantiations: 3738
% 5.00/1.96  #Strategies tried      : 1
% 5.00/1.96  
% 5.00/1.96  Timing (in seconds)
% 5.00/1.96  ----------------------
% 5.00/1.97  Preprocessing        : 0.31
% 5.00/1.97  Parsing              : 0.16
% 5.00/1.97  CNF conversion       : 0.02
% 5.00/1.97  Main loop            : 0.90
% 5.00/1.97  Inferencing          : 0.43
% 5.00/1.97  Reduction            : 0.23
% 5.00/1.97  Demodulation         : 0.16
% 5.00/1.97  BG Simplification    : 0.05
% 5.00/1.97  Subsumption          : 0.14
% 5.00/1.97  Abstraction          : 0.05
% 5.00/1.97  MUC search           : 0.00
% 5.00/1.97  Cooper               : 0.00
% 5.00/1.97  Total                : 1.23
% 5.00/1.97  Index Insertion      : 0.00
% 5.00/1.97  Index Deletion       : 0.00
% 5.00/1.97  Index Matching       : 0.00
% 5.00/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
