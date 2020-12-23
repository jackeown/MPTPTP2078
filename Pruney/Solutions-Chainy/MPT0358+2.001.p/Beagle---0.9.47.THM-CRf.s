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
% DateTime   : Thu Dec  3 09:56:00 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 133 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 206 expanded)
%              Number of equality atoms :   34 (  94 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_32,plain,(
    ! [A_16] : k1_subset_1(A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44])).

tff(c_169,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_63,plain,(
    ! [B_21,A_22] : k2_xboole_0(B_21,A_22) = k2_xboole_0(A_22,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,(
    ! [A_22] : k2_xboole_0(k1_xboole_0,A_22) = A_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_28])).

tff(c_147,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_154,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_147])).

tff(c_279,plain,(
    ! [A_22] : k4_xboole_0('#skF_4',A_22) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_169,c_154])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_346,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_22])).

tff(c_38,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_45,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_277,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_45])).

tff(c_349,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_346,c_277])).

tff(c_353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_349])).

tff(c_355,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_163,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_147])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_700,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r2_hidden('#skF_1'(A_80,B_81,C_82),B_81)
      | r2_hidden('#skF_2'(A_80,B_81,C_82),C_82)
      | k4_xboole_0(A_80,B_81) = C_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_709,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k4_xboole_0(A_3,A_3) = C_5 ) ),
    inference(resolution,[status(thm)],[c_20,c_700])).

tff(c_722,plain,(
    ! [A_83,C_84] :
      ( r2_hidden('#skF_2'(A_83,A_83,C_84),C_84)
      | k1_xboole_0 = C_84 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_709])).

tff(c_354,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_427,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_435,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_354,c_427])).

tff(c_500,plain,(
    ! [D_61,A_62,B_63] :
      ( r2_hidden(D_61,k4_xboole_0(A_62,B_63))
      | r2_hidden(D_61,B_63)
      | ~ r2_hidden(D_61,A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_655,plain,(
    ! [D_76] :
      ( r2_hidden(D_76,k1_xboole_0)
      | r2_hidden(D_76,k3_subset_1('#skF_3','#skF_4'))
      | ~ r2_hidden(D_76,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_500])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_483,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k3_subset_1(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_487,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_483])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_491,plain,(
    ! [D_8] :
      ( ~ r2_hidden(D_8,'#skF_4')
      | ~ r2_hidden(D_8,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_6])).

tff(c_665,plain,(
    ! [D_76] :
      ( r2_hidden(D_76,k1_xboole_0)
      | ~ r2_hidden(D_76,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_655,c_491])).

tff(c_667,plain,(
    ! [D_77] :
      ( r2_hidden(D_77,k1_xboole_0)
      | ~ r2_hidden(D_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_655,c_491])).

tff(c_466,plain,(
    ! [D_52,B_53,A_54] :
      ( ~ r2_hidden(D_52,B_53)
      | ~ r2_hidden(D_52,k4_xboole_0(A_54,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_478,plain,(
    ! [D_52,A_13] :
      ( ~ r2_hidden(D_52,A_13)
      | ~ r2_hidden(D_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_466])).

tff(c_674,plain,(
    ! [D_78] :
      ( ~ r2_hidden(D_78,k1_xboole_0)
      | ~ r2_hidden(D_78,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_667,c_478])).

tff(c_686,plain,(
    ! [D_76] : ~ r2_hidden(D_76,'#skF_4') ),
    inference(resolution,[status(thm)],[c_665,c_674])).

tff(c_726,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_722,c_686])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.46  
% 2.44/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.46  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.44/1.46  
% 2.44/1.46  %Foreground sorts:
% 2.44/1.46  
% 2.44/1.46  
% 2.44/1.46  %Background operators:
% 2.44/1.46  
% 2.44/1.46  
% 2.44/1.46  %Foreground operators:
% 2.44/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.44/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.44/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.44/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.44/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.44/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.46  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.44/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.44/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.46  
% 2.83/1.48  tff(f_49, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.83/1.48  tff(f_60, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.83/1.48  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.83/1.48  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.83/1.48  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.83/1.48  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.83/1.48  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.83/1.48  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.83/1.48  tff(c_32, plain, (![A_16]: (k1_subset_1(A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.48  tff(c_44, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.83/1.48  tff(c_46, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44])).
% 2.83/1.48  tff(c_169, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 2.83/1.48  tff(c_63, plain, (![B_21, A_22]: (k2_xboole_0(B_21, A_22)=k2_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.48  tff(c_28, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.48  tff(c_79, plain, (![A_22]: (k2_xboole_0(k1_xboole_0, A_22)=A_22)), inference(superposition, [status(thm), theory('equality')], [c_63, c_28])).
% 2.83/1.48  tff(c_147, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.83/1.48  tff(c_154, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79, c_147])).
% 2.83/1.48  tff(c_279, plain, (![A_22]: (k4_xboole_0('#skF_4', A_22)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_169, c_154])).
% 2.83/1.48  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.48  tff(c_346, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | k4_xboole_0(A_35, B_36)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_22])).
% 2.83/1.48  tff(c_38, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.83/1.48  tff(c_45, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38])).
% 2.83/1.48  tff(c_277, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_45])).
% 2.83/1.48  tff(c_349, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_346, c_277])).
% 2.83/1.48  tff(c_353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_279, c_349])).
% 2.83/1.48  tff(c_355, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.83/1.48  tff(c_163, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_147])).
% 2.83/1.48  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.48  tff(c_700, plain, (![A_80, B_81, C_82]: (~r2_hidden('#skF_1'(A_80, B_81, C_82), B_81) | r2_hidden('#skF_2'(A_80, B_81, C_82), C_82) | k4_xboole_0(A_80, B_81)=C_82)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.48  tff(c_709, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k4_xboole_0(A_3, A_3)=C_5)), inference(resolution, [status(thm)], [c_20, c_700])).
% 2.83/1.48  tff(c_722, plain, (![A_83, C_84]: (r2_hidden('#skF_2'(A_83, A_83, C_84), C_84) | k1_xboole_0=C_84)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_709])).
% 2.83/1.48  tff(c_354, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 2.83/1.48  tff(c_427, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.48  tff(c_435, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_354, c_427])).
% 2.83/1.48  tff(c_500, plain, (![D_61, A_62, B_63]: (r2_hidden(D_61, k4_xboole_0(A_62, B_63)) | r2_hidden(D_61, B_63) | ~r2_hidden(D_61, A_62))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.48  tff(c_655, plain, (![D_76]: (r2_hidden(D_76, k1_xboole_0) | r2_hidden(D_76, k3_subset_1('#skF_3', '#skF_4')) | ~r2_hidden(D_76, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_435, c_500])).
% 2.83/1.48  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.83/1.48  tff(c_483, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k3_subset_1(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.48  tff(c_487, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_483])).
% 2.83/1.48  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.48  tff(c_491, plain, (![D_8]: (~r2_hidden(D_8, '#skF_4') | ~r2_hidden(D_8, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_487, c_6])).
% 2.83/1.48  tff(c_665, plain, (![D_76]: (r2_hidden(D_76, k1_xboole_0) | ~r2_hidden(D_76, '#skF_4'))), inference(resolution, [status(thm)], [c_655, c_491])).
% 2.83/1.48  tff(c_667, plain, (![D_77]: (r2_hidden(D_77, k1_xboole_0) | ~r2_hidden(D_77, '#skF_4'))), inference(resolution, [status(thm)], [c_655, c_491])).
% 2.83/1.48  tff(c_466, plain, (![D_52, B_53, A_54]: (~r2_hidden(D_52, B_53) | ~r2_hidden(D_52, k4_xboole_0(A_54, B_53)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.48  tff(c_478, plain, (![D_52, A_13]: (~r2_hidden(D_52, A_13) | ~r2_hidden(D_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_163, c_466])).
% 2.83/1.48  tff(c_674, plain, (![D_78]: (~r2_hidden(D_78, k1_xboole_0) | ~r2_hidden(D_78, '#skF_4'))), inference(resolution, [status(thm)], [c_667, c_478])).
% 2.83/1.48  tff(c_686, plain, (![D_76]: (~r2_hidden(D_76, '#skF_4'))), inference(resolution, [status(thm)], [c_665, c_674])).
% 2.83/1.48  tff(c_726, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_722, c_686])).
% 2.83/1.48  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_355, c_726])).
% 2.83/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.48  
% 2.83/1.48  Inference rules
% 2.83/1.48  ----------------------
% 2.83/1.48  #Ref     : 0
% 2.83/1.48  #Sup     : 170
% 2.83/1.48  #Fact    : 0
% 2.83/1.48  #Define  : 0
% 2.83/1.48  #Split   : 1
% 2.83/1.48  #Chain   : 0
% 2.83/1.48  #Close   : 0
% 2.83/1.48  
% 2.83/1.48  Ordering : KBO
% 2.83/1.48  
% 2.83/1.48  Simplification rules
% 2.83/1.48  ----------------------
% 2.83/1.48  #Subsume      : 25
% 2.83/1.48  #Demod        : 44
% 2.83/1.48  #Tautology    : 102
% 2.83/1.48  #SimpNegUnit  : 2
% 2.83/1.48  #BackRed      : 5
% 2.83/1.48  
% 2.83/1.48  #Partial instantiations: 0
% 2.83/1.48  #Strategies tried      : 1
% 2.83/1.48  
% 2.83/1.48  Timing (in seconds)
% 2.83/1.48  ----------------------
% 2.83/1.48  Preprocessing        : 0.33
% 2.83/1.48  Parsing              : 0.17
% 2.83/1.48  CNF conversion       : 0.02
% 2.83/1.48  Main loop            : 0.33
% 2.83/1.48  Inferencing          : 0.12
% 2.83/1.48  Reduction            : 0.10
% 2.83/1.48  Demodulation         : 0.08
% 2.83/1.48  BG Simplification    : 0.02
% 2.83/1.48  Subsumption          : 0.06
% 2.83/1.48  Abstraction          : 0.02
% 2.83/1.48  MUC search           : 0.00
% 2.83/1.48  Cooper               : 0.00
% 2.83/1.48  Total                : 0.69
% 2.83/1.48  Index Insertion      : 0.00
% 2.83/1.48  Index Deletion       : 0.00
% 2.87/1.48  Index Matching       : 0.00
% 2.87/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
