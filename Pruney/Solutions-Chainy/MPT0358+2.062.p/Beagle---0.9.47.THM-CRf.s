%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:08 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 131 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :   74 ( 191 expanded)
%              Number of equality atoms :   28 (  92 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_30,plain,(
    ! [A_16] : k1_subset_1(A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_26,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,(
    ! [A_13] : r1_tarski('#skF_5',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_26])).

tff(c_36,plain,
    ( k1_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_43,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_59,c_43])).

tff(c_81,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    k3_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_81,c_24])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,(
    ! [D_32,B_33,A_34] :
      ( ~ r2_hidden(D_32,B_33)
      | ~ r2_hidden(D_32,k4_xboole_0(A_34,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_392,plain,(
    ! [D_61,A_62,B_63] :
      ( ~ r2_hidden(D_61,k4_xboole_0(A_62,B_63))
      | ~ r2_hidden(D_61,k3_xboole_0(A_62,B_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_124])).

tff(c_3900,plain,(
    ! [D_180,A_181,B_182] :
      ( ~ r2_hidden(D_180,k3_xboole_0(A_181,B_182))
      | r2_hidden(D_180,B_182)
      | ~ r2_hidden(D_180,A_181) ) ),
    inference(resolution,[status(thm)],[c_2,c_392])).

tff(c_4047,plain,(
    ! [D_187] :
      ( ~ r2_hidden(D_187,'#skF_5')
      | r2_hidden(D_187,k3_subset_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_187,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_3900])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_225,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k3_subset_1(A_39,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_229,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_225])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_233,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_5')
      | ~ r2_hidden(D_6,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_4])).

tff(c_4089,plain,(
    ! [D_187] : ~ r2_hidden(D_187,'#skF_5') ),
    inference(resolution,[status(thm)],[c_4047,c_233])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_133,plain,(
    ! [A_35,B_36] : k5_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_142,plain,(
    k4_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = k5_xboole_0('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_133])).

tff(c_157,plain,(
    k4_xboole_0('#skF_5',k5_xboole_0('#skF_5','#skF_5')) = k3_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_28])).

tff(c_160,plain,(
    k4_xboole_0('#skF_5',k5_xboole_0('#skF_5','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_157])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [D_29,A_30,B_31] :
      ( r2_hidden(D_29,A_30)
      | ~ r2_hidden(D_29,k4_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_423,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_64,B_65)),A_64)
      | k4_xboole_0(A_64,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_115])).

tff(c_470,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_5')
    | k4_xboole_0('#skF_5',k5_xboole_0('#skF_5','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_423])).

tff(c_497,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_470])).

tff(c_498,plain,(
    r2_hidden('#skF_3'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_497])).

tff(c_4092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4089,c_498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.96  
% 5.14/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.96  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 5.14/1.96  
% 5.14/1.96  %Foreground sorts:
% 5.14/1.96  
% 5.14/1.96  
% 5.14/1.96  %Background operators:
% 5.14/1.96  
% 5.14/1.96  
% 5.14/1.96  %Foreground operators:
% 5.14/1.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.14/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.14/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.14/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.14/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.14/1.96  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.14/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.14/1.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.14/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.14/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.14/1.96  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.14/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/1.96  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.14/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.14/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.14/1.96  
% 5.28/1.98  tff(f_55, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 5.28/1.98  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 5.28/1.98  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.28/1.98  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.28/1.98  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.28/1.98  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.28/1.98  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.28/1.98  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.28/1.98  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.28/1.98  tff(c_30, plain, (![A_16]: (k1_subset_1(A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.28/1.98  tff(c_42, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.28/1.98  tff(c_44, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42])).
% 5.28/1.98  tff(c_59, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_44])).
% 5.28/1.98  tff(c_26, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.28/1.98  tff(c_61, plain, (![A_13]: (r1_tarski('#skF_5', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_26])).
% 5.28/1.98  tff(c_36, plain, (k1_subset_1('#skF_4')!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.28/1.98  tff(c_43, plain, (k1_xboole_0!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36])).
% 5.28/1.98  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_59, c_43])).
% 5.28/1.98  tff(c_81, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_44])).
% 5.28/1.98  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.28/1.98  tff(c_93, plain, (k3_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_81, c_24])).
% 5.28/1.98  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.28/1.98  tff(c_28, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.28/1.98  tff(c_124, plain, (![D_32, B_33, A_34]: (~r2_hidden(D_32, B_33) | ~r2_hidden(D_32, k4_xboole_0(A_34, B_33)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.28/1.98  tff(c_392, plain, (![D_61, A_62, B_63]: (~r2_hidden(D_61, k4_xboole_0(A_62, B_63)) | ~r2_hidden(D_61, k3_xboole_0(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_124])).
% 5.28/1.98  tff(c_3900, plain, (![D_180, A_181, B_182]: (~r2_hidden(D_180, k3_xboole_0(A_181, B_182)) | r2_hidden(D_180, B_182) | ~r2_hidden(D_180, A_181))), inference(resolution, [status(thm)], [c_2, c_392])).
% 5.28/1.98  tff(c_4047, plain, (![D_187]: (~r2_hidden(D_187, '#skF_5') | r2_hidden(D_187, k3_subset_1('#skF_4', '#skF_5')) | ~r2_hidden(D_187, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_3900])).
% 5.28/1.98  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.28/1.98  tff(c_225, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k3_subset_1(A_39, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.28/1.98  tff(c_229, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_225])).
% 5.28/1.98  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.28/1.98  tff(c_233, plain, (![D_6]: (~r2_hidden(D_6, '#skF_5') | ~r2_hidden(D_6, k3_subset_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_229, c_4])).
% 5.28/1.98  tff(c_4089, plain, (![D_187]: (~r2_hidden(D_187, '#skF_5'))), inference(resolution, [status(thm)], [c_4047, c_233])).
% 5.28/1.98  tff(c_82, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 5.28/1.98  tff(c_133, plain, (![A_35, B_36]: (k5_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.28/1.98  tff(c_142, plain, (k4_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))=k5_xboole_0('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_93, c_133])).
% 5.28/1.98  tff(c_157, plain, (k4_xboole_0('#skF_5', k5_xboole_0('#skF_5', '#skF_5'))=k3_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_28])).
% 5.28/1.98  tff(c_160, plain, (k4_xboole_0('#skF_5', k5_xboole_0('#skF_5', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_157])).
% 5.28/1.98  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.28/1.98  tff(c_115, plain, (![D_29, A_30, B_31]: (r2_hidden(D_29, A_30) | ~r2_hidden(D_29, k4_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.28/1.98  tff(c_423, plain, (![A_64, B_65]: (r2_hidden('#skF_3'(k4_xboole_0(A_64, B_65)), A_64) | k4_xboole_0(A_64, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_115])).
% 5.28/1.98  tff(c_470, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_5') | k4_xboole_0('#skF_5', k5_xboole_0('#skF_5', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_160, c_423])).
% 5.28/1.98  tff(c_497, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_470])).
% 5.28/1.98  tff(c_498, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_82, c_497])).
% 5.28/1.98  tff(c_4092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4089, c_498])).
% 5.28/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/1.98  
% 5.28/1.98  Inference rules
% 5.28/1.98  ----------------------
% 5.28/1.98  #Ref     : 0
% 5.28/1.98  #Sup     : 906
% 5.28/1.98  #Fact    : 2
% 5.28/1.98  #Define  : 0
% 5.28/1.98  #Split   : 5
% 5.28/1.98  #Chain   : 0
% 5.28/1.98  #Close   : 0
% 5.28/1.98  
% 5.28/1.98  Ordering : KBO
% 5.28/1.98  
% 5.28/1.98  Simplification rules
% 5.28/1.98  ----------------------
% 5.28/1.98  #Subsume      : 147
% 5.28/1.98  #Demod        : 546
% 5.28/1.98  #Tautology    : 316
% 5.28/1.98  #SimpNegUnit  : 21
% 5.28/1.98  #BackRed      : 43
% 5.28/1.98  
% 5.28/1.98  #Partial instantiations: 0
% 5.28/1.98  #Strategies tried      : 1
% 5.28/1.98  
% 5.28/1.98  Timing (in seconds)
% 5.28/1.98  ----------------------
% 5.28/1.98  Preprocessing        : 0.31
% 5.28/1.98  Parsing              : 0.16
% 5.28/1.98  CNF conversion       : 0.02
% 5.28/1.98  Main loop            : 0.90
% 5.28/1.98  Inferencing          : 0.30
% 5.28/1.98  Reduction            : 0.30
% 5.28/1.98  Demodulation         : 0.22
% 5.28/1.98  BG Simplification    : 0.04
% 5.28/1.98  Subsumption          : 0.19
% 5.28/1.98  Abstraction          : 0.05
% 5.28/1.98  MUC search           : 0.00
% 5.28/1.98  Cooper               : 0.00
% 5.28/1.98  Total                : 1.24
% 5.28/1.98  Index Insertion      : 0.00
% 5.28/1.98  Index Deletion       : 0.00
% 5.28/1.98  Index Matching       : 0.00
% 5.28/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
