%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:29 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   70 (  80 expanded)
%              Number of leaves         :   38 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 105 expanded)
%              Number of equality atoms :   26 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_127,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_424,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(B_74,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_127])).

tff(c_26,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_436,plain,(
    ! [B_74,A_73] : k2_xboole_0(B_74,A_73) = k2_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_26])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( k2_xboole_0(k4_xboole_0(B_23,k1_tarski(A_22)),k1_tarski(A_22)) = B_23
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_577,plain,(
    ! [A_86,B_87] :
      ( k2_xboole_0(k1_tarski(A_86),B_87) = B_87
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_436,c_28])).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_51,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32])).

tff(c_633,plain,(
    ! [B_88,A_89] :
      ( B_88 != '#skF_3'
      | ~ r2_hidden(A_89,B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_51])).

tff(c_638,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_633])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_9] : r1_tarski('#skF_3',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_30,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_30])).

tff(c_123,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,k3_tarski(B_45))
      | ~ m1_setfam_1(B_45,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,'#skF_3')
      | ~ m1_setfam_1('#skF_3',A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_123])).

tff(c_327,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_329,plain,(
    ! [A_44] :
      ( A_44 = '#skF_3'
      | ~ r1_tarski('#skF_3',A_44)
      | ~ m1_setfam_1('#skF_3',A_44) ) ),
    inference(resolution,[status(thm)],[c_126,c_327])).

tff(c_362,plain,(
    ! [A_68] :
      ( A_68 = '#skF_3'
      | ~ m1_setfam_1('#skF_3',A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_329])).

tff(c_378,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_362])).

tff(c_40,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(u1_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_385,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_40])).

tff(c_389,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_385])).

tff(c_390,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_389])).

tff(c_641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.34  
% 2.51/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.35  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.51/1.35  
% 2.51/1.35  %Foreground sorts:
% 2.51/1.35  
% 2.51/1.35  
% 2.51/1.35  %Background operators:
% 2.51/1.35  
% 2.51/1.35  
% 2.51/1.35  %Foreground operators:
% 2.51/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.35  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.51/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.51/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.51/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.51/1.35  
% 2.51/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.51/1.36  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.51/1.36  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.51/1.36  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.51/1.36  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 2.51/1.36  tff(f_89, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 2.51/1.36  tff(f_61, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.51/1.36  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.51/1.36  tff(f_58, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.51/1.36  tff(f_65, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.51/1.36  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.51/1.36  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.51/1.36  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.36  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.36  tff(c_18, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.51/1.36  tff(c_127, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.51/1.36  tff(c_424, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(B_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_18, c_127])).
% 2.51/1.36  tff(c_26, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.51/1.36  tff(c_436, plain, (![B_74, A_73]: (k2_xboole_0(B_74, A_73)=k2_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_424, c_26])).
% 2.51/1.36  tff(c_28, plain, (![B_23, A_22]: (k2_xboole_0(k4_xboole_0(B_23, k1_tarski(A_22)), k1_tarski(A_22))=B_23 | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.51/1.36  tff(c_577, plain, (![A_86, B_87]: (k2_xboole_0(k1_tarski(A_86), B_87)=B_87 | ~r2_hidden(A_86, B_87))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_436, c_28])).
% 2.51/1.36  tff(c_42, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.51/1.36  tff(c_32, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.51/1.36  tff(c_51, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32])).
% 2.51/1.36  tff(c_633, plain, (![B_88, A_89]: (B_88!='#skF_3' | ~r2_hidden(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_577, c_51])).
% 2.51/1.36  tff(c_638, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_633])).
% 2.51/1.36  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.51/1.36  tff(c_48, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.51/1.36  tff(c_44, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.51/1.36  tff(c_14, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.36  tff(c_53, plain, (![A_9]: (r1_tarski('#skF_3', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 2.51/1.36  tff(c_30, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.51/1.36  tff(c_52, plain, (k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_30])).
% 2.51/1.36  tff(c_123, plain, (![A_44, B_45]: (r1_tarski(A_44, k3_tarski(B_45)) | ~m1_setfam_1(B_45, A_44))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.51/1.36  tff(c_126, plain, (![A_44]: (r1_tarski(A_44, '#skF_3') | ~m1_setfam_1('#skF_3', A_44))), inference(superposition, [status(thm), theory('equality')], [c_52, c_123])).
% 2.51/1.36  tff(c_327, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.36  tff(c_329, plain, (![A_44]: (A_44='#skF_3' | ~r1_tarski('#skF_3', A_44) | ~m1_setfam_1('#skF_3', A_44))), inference(resolution, [status(thm)], [c_126, c_327])).
% 2.51/1.36  tff(c_362, plain, (![A_68]: (A_68='#skF_3' | ~m1_setfam_1('#skF_3', A_68))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_329])).
% 2.51/1.36  tff(c_378, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_44, c_362])).
% 2.51/1.36  tff(c_40, plain, (![A_30]: (~v1_xboole_0(u1_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.36  tff(c_385, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_378, c_40])).
% 2.51/1.36  tff(c_389, plain, (~v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_385])).
% 2.51/1.36  tff(c_390, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_389])).
% 2.51/1.36  tff(c_641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_638, c_390])).
% 2.51/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  Inference rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Ref     : 0
% 2.51/1.36  #Sup     : 143
% 2.51/1.36  #Fact    : 0
% 2.51/1.36  #Define  : 0
% 2.51/1.36  #Split   : 0
% 2.51/1.36  #Chain   : 0
% 2.51/1.36  #Close   : 0
% 2.51/1.36  
% 2.51/1.36  Ordering : KBO
% 2.51/1.36  
% 2.51/1.36  Simplification rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Subsume      : 10
% 2.51/1.36  #Demod        : 36
% 2.51/1.36  #Tautology    : 86
% 2.51/1.36  #SimpNegUnit  : 1
% 2.51/1.36  #BackRed      : 3
% 2.51/1.36  
% 2.51/1.36  #Partial instantiations: 0
% 2.51/1.36  #Strategies tried      : 1
% 2.51/1.36  
% 2.51/1.36  Timing (in seconds)
% 2.51/1.36  ----------------------
% 2.51/1.36  Preprocessing        : 0.32
% 2.51/1.36  Parsing              : 0.18
% 2.51/1.36  CNF conversion       : 0.02
% 2.51/1.36  Main loop            : 0.26
% 2.51/1.36  Inferencing          : 0.10
% 2.51/1.36  Reduction            : 0.09
% 2.51/1.36  Demodulation         : 0.07
% 2.51/1.36  BG Simplification    : 0.02
% 2.51/1.36  Subsumption          : 0.04
% 2.51/1.36  Abstraction          : 0.01
% 2.51/1.36  MUC search           : 0.00
% 2.51/1.36  Cooper               : 0.00
% 2.51/1.36  Total                : 0.61
% 2.51/1.36  Index Insertion      : 0.00
% 2.51/1.36  Index Deletion       : 0.00
% 2.51/1.36  Index Matching       : 0.00
% 2.51/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
