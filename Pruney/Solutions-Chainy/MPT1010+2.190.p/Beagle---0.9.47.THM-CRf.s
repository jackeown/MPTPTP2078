%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:30 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   59 (  65 expanded)
%              Number of leaves         :   37 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  86 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_48,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_124,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_124])).

tff(c_136,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_133])).

tff(c_40,plain,(
    ! [B_41] : k4_xboole_0(k1_tarski(B_41),k1_tarski(B_41)) != k1_tarski(B_41) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_137,plain,(
    ! [B_41] : k1_tarski(B_41) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_40])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3575,plain,(
    ! [D_20937,C_20938,B_20939,A_20940] :
      ( r2_hidden(k1_funct_1(D_20937,C_20938),B_20939)
      | k1_xboole_0 = B_20939
      | ~ r2_hidden(C_20938,A_20940)
      | ~ m1_subset_1(D_20937,k1_zfmisc_1(k2_zfmisc_1(A_20940,B_20939)))
      | ~ v1_funct_2(D_20937,A_20940,B_20939)
      | ~ v1_funct_1(D_20937) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4400,plain,(
    ! [D_25276,B_25277] :
      ( r2_hidden(k1_funct_1(D_25276,'#skF_5'),B_25277)
      | k1_xboole_0 = B_25277
      | ~ m1_subset_1(D_25276,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_25277)))
      | ~ v1_funct_2(D_25276,'#skF_3',B_25277)
      | ~ v1_funct_1(D_25276) ) ),
    inference(resolution,[status(thm)],[c_50,c_3575])).

tff(c_4417,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_4400])).

tff(c_4420,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4417])).

tff(c_4421,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_4420])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_146,plain,(
    ! [D_66,B_67,A_68] :
      ( D_66 = B_67
      | D_66 = A_68
      | ~ r2_hidden(D_66,k2_tarski(A_68,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_149,plain,(
    ! [D_66,A_12] :
      ( D_66 = A_12
      | D_66 = A_12
      | ~ r2_hidden(D_66,k1_tarski(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_146])).

tff(c_4428,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4421,c_149])).

tff(c_4490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_4428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:33:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.88  
% 4.50/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.89  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.50/1.89  
% 4.50/1.89  %Foreground sorts:
% 4.50/1.89  
% 4.50/1.89  
% 4.50/1.89  %Background operators:
% 4.50/1.89  
% 4.50/1.89  
% 4.50/1.89  %Foreground operators:
% 4.50/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.50/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.50/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.50/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.50/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.50/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.50/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.50/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.50/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.50/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.50/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.50/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.50/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.50/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.50/1.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.50/1.89  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.50/1.89  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.50/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.50/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/1.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.50/1.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.50/1.89  
% 4.50/1.90  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 4.50/1.90  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.50/1.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.50/1.90  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.50/1.90  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.50/1.90  tff(f_73, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 4.50/1.90  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.50/1.90  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.50/1.90  tff(c_48, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.50/1.90  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.90  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/1.90  tff(c_124, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.50/1.90  tff(c_133, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_124])).
% 4.50/1.90  tff(c_136, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_133])).
% 4.50/1.90  tff(c_40, plain, (![B_41]: (k4_xboole_0(k1_tarski(B_41), k1_tarski(B_41))!=k1_tarski(B_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.50/1.90  tff(c_137, plain, (![B_41]: (k1_tarski(B_41)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_40])).
% 4.50/1.90  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.50/1.90  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.50/1.90  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.50/1.90  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.50/1.90  tff(c_3575, plain, (![D_20937, C_20938, B_20939, A_20940]: (r2_hidden(k1_funct_1(D_20937, C_20938), B_20939) | k1_xboole_0=B_20939 | ~r2_hidden(C_20938, A_20940) | ~m1_subset_1(D_20937, k1_zfmisc_1(k2_zfmisc_1(A_20940, B_20939))) | ~v1_funct_2(D_20937, A_20940, B_20939) | ~v1_funct_1(D_20937))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.90  tff(c_4400, plain, (![D_25276, B_25277]: (r2_hidden(k1_funct_1(D_25276, '#skF_5'), B_25277) | k1_xboole_0=B_25277 | ~m1_subset_1(D_25276, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_25277))) | ~v1_funct_2(D_25276, '#skF_3', B_25277) | ~v1_funct_1(D_25276))), inference(resolution, [status(thm)], [c_50, c_3575])).
% 4.50/1.90  tff(c_4417, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_4400])).
% 4.50/1.90  tff(c_4420, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4417])).
% 4.50/1.90  tff(c_4421, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_137, c_4420])).
% 4.50/1.90  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.50/1.90  tff(c_146, plain, (![D_66, B_67, A_68]: (D_66=B_67 | D_66=A_68 | ~r2_hidden(D_66, k2_tarski(A_68, B_67)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.50/1.90  tff(c_149, plain, (![D_66, A_12]: (D_66=A_12 | D_66=A_12 | ~r2_hidden(D_66, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_146])).
% 4.50/1.90  tff(c_4428, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_4421, c_149])).
% 4.50/1.90  tff(c_4490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_4428])).
% 4.50/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.90  
% 4.50/1.90  Inference rules
% 4.50/1.90  ----------------------
% 4.50/1.90  #Ref     : 0
% 4.50/1.90  #Sup     : 493
% 4.50/1.90  #Fact    : 8
% 4.50/1.90  #Define  : 0
% 4.50/1.90  #Split   : 5
% 4.50/1.90  #Chain   : 0
% 4.50/1.90  #Close   : 0
% 4.50/1.90  
% 4.50/1.90  Ordering : KBO
% 4.50/1.90  
% 4.50/1.90  Simplification rules
% 4.50/1.90  ----------------------
% 4.50/1.90  #Subsume      : 77
% 4.50/1.90  #Demod        : 75
% 4.50/1.90  #Tautology    : 172
% 4.50/1.90  #SimpNegUnit  : 23
% 4.50/1.90  #BackRed      : 1
% 4.50/1.90  
% 4.50/1.90  #Partial instantiations: 6386
% 4.50/1.90  #Strategies tried      : 1
% 4.50/1.90  
% 4.50/1.90  Timing (in seconds)
% 4.50/1.90  ----------------------
% 4.50/1.90  Preprocessing        : 0.34
% 4.50/1.90  Parsing              : 0.19
% 4.50/1.90  CNF conversion       : 0.02
% 4.50/1.90  Main loop            : 0.77
% 4.50/1.90  Inferencing          : 0.46
% 4.50/1.90  Reduction            : 0.14
% 4.50/1.90  Demodulation         : 0.10
% 4.50/1.90  BG Simplification    : 0.03
% 4.50/1.90  Subsumption          : 0.09
% 4.50/1.90  Abstraction          : 0.04
% 4.50/1.90  MUC search           : 0.00
% 4.50/1.90  Cooper               : 0.00
% 4.50/1.90  Total                : 1.14
% 4.50/1.90  Index Insertion      : 0.00
% 4.50/1.90  Index Deletion       : 0.00
% 4.50/1.90  Index Matching       : 0.00
% 4.50/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
