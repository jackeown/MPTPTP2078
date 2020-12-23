%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:34 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   58 (  83 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :   71 ( 130 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k3_mcart_1 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2])).

tff(c_32,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_42,plain,(
    ! [A_1] : m1_subset_1('#skF_3',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4])).

tff(c_88,plain,(
    ! [A_47,B_48] :
      ( k5_setfam_1(A_47,B_48) = k3_tarski(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_98,plain,(
    ! [A_47] : k5_setfam_1(A_47,'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_117,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k5_setfam_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [A_47] :
      ( m1_subset_1(k3_tarski('#skF_3'),k1_zfmisc_1(A_47))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_117])).

tff(c_135,plain,(
    ! [A_57] : m1_subset_1(k3_tarski('#skF_3'),k1_zfmisc_1(A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_129])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_148,plain,(
    ! [A_58] : r1_tarski(k3_tarski('#skF_3'),A_58) ),
    inference(resolution,[status(thm)],[c_135,c_10])).

tff(c_22,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_51,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_1'(A_34),A_34)
      | A_34 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_55,plain,(
    ! [A_34] :
      ( ~ r1_tarski(A_34,'#skF_1'(A_34))
      | A_34 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_51,c_20])).

tff(c_158,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_148,c_55])).

tff(c_161,plain,(
    ! [A_47] : k5_setfam_1(A_47,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_98])).

tff(c_188,plain,(
    ! [A_67,B_68] :
      ( k5_setfam_1(A_67,B_68) = A_67
      | ~ m1_setfam_1(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_200,plain,(
    ! [A_67] :
      ( k5_setfam_1(A_67,'#skF_3') = A_67
      | ~ m1_setfam_1('#skF_3',A_67) ) ),
    inference(resolution,[status(thm)],[c_42,c_188])).

tff(c_205,plain,(
    ! [A_69] :
      ( A_69 = '#skF_3'
      | ~ m1_setfam_1('#skF_3',A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_200])).

tff(c_209,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_205])).

tff(c_28,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(u1_struct_0(A_29))
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_214,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_28])).

tff(c_218,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_44,c_214])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.20  
% 2.01/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k3_mcart_1 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.01/1.20  
% 2.01/1.20  %Foreground sorts:
% 2.01/1.20  
% 2.01/1.20  
% 2.01/1.20  %Background operators:
% 2.01/1.20  
% 2.01/1.20  
% 2.01/1.20  %Foreground operators:
% 2.01/1.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.01/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.01/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.20  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.01/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.20  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.01/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.01/1.20  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.01/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.01/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.01/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.20  
% 2.01/1.22  tff(f_95, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 2.01/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.01/1.22  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.01/1.22  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.01/1.22  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.01/1.22  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.01/1.22  tff(f_73, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.01/1.22  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.01/1.22  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.01/1.22  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.01/1.22  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.01/1.22  tff(c_36, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.01/1.22  tff(c_30, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.01/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.01/1.22  tff(c_44, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2])).
% 2.01/1.22  tff(c_32, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.01/1.22  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.01/1.22  tff(c_42, plain, (![A_1]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4])).
% 2.01/1.22  tff(c_88, plain, (![A_47, B_48]: (k5_setfam_1(A_47, B_48)=k3_tarski(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.01/1.22  tff(c_98, plain, (![A_47]: (k5_setfam_1(A_47, '#skF_3')=k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_88])).
% 2.01/1.22  tff(c_117, plain, (![A_55, B_56]: (m1_subset_1(k5_setfam_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.01/1.22  tff(c_129, plain, (![A_47]: (m1_subset_1(k3_tarski('#skF_3'), k1_zfmisc_1(A_47)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(superposition, [status(thm), theory('equality')], [c_98, c_117])).
% 2.01/1.22  tff(c_135, plain, (![A_57]: (m1_subset_1(k3_tarski('#skF_3'), k1_zfmisc_1(A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_129])).
% 2.01/1.22  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.01/1.22  tff(c_148, plain, (![A_58]: (r1_tarski(k3_tarski('#skF_3'), A_58))), inference(resolution, [status(thm)], [c_135, c_10])).
% 2.01/1.22  tff(c_22, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.01/1.22  tff(c_51, plain, (![A_34]: (r2_hidden('#skF_1'(A_34), A_34) | A_34='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22])).
% 2.01/1.22  tff(c_20, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.22  tff(c_55, plain, (![A_34]: (~r1_tarski(A_34, '#skF_1'(A_34)) | A_34='#skF_3')), inference(resolution, [status(thm)], [c_51, c_20])).
% 2.01/1.22  tff(c_158, plain, (k3_tarski('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_148, c_55])).
% 2.01/1.22  tff(c_161, plain, (![A_47]: (k5_setfam_1(A_47, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_98])).
% 2.01/1.22  tff(c_188, plain, (![A_67, B_68]: (k5_setfam_1(A_67, B_68)=A_67 | ~m1_setfam_1(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.01/1.22  tff(c_200, plain, (![A_67]: (k5_setfam_1(A_67, '#skF_3')=A_67 | ~m1_setfam_1('#skF_3', A_67))), inference(resolution, [status(thm)], [c_42, c_188])).
% 2.01/1.22  tff(c_205, plain, (![A_69]: (A_69='#skF_3' | ~m1_setfam_1('#skF_3', A_69))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_200])).
% 2.01/1.22  tff(c_209, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_32, c_205])).
% 2.01/1.22  tff(c_28, plain, (![A_29]: (~v1_xboole_0(u1_struct_0(A_29)) | ~l1_struct_0(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.01/1.22  tff(c_214, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_209, c_28])).
% 2.01/1.22  tff(c_218, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_44, c_214])).
% 2.01/1.22  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_218])).
% 2.01/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.22  
% 2.01/1.22  Inference rules
% 2.01/1.22  ----------------------
% 2.01/1.22  #Ref     : 0
% 2.01/1.22  #Sup     : 37
% 2.01/1.22  #Fact    : 0
% 2.01/1.22  #Define  : 0
% 2.01/1.22  #Split   : 0
% 2.01/1.22  #Chain   : 0
% 2.01/1.22  #Close   : 0
% 2.01/1.22  
% 2.01/1.22  Ordering : KBO
% 2.01/1.22  
% 2.01/1.22  Simplification rules
% 2.01/1.22  ----------------------
% 2.01/1.22  #Subsume      : 1
% 2.01/1.22  #Demod        : 28
% 2.01/1.22  #Tautology    : 19
% 2.01/1.22  #SimpNegUnit  : 1
% 2.01/1.22  #BackRed      : 4
% 2.01/1.22  
% 2.01/1.22  #Partial instantiations: 0
% 2.01/1.22  #Strategies tried      : 1
% 2.01/1.22  
% 2.01/1.22  Timing (in seconds)
% 2.01/1.22  ----------------------
% 2.01/1.22  Preprocessing        : 0.30
% 2.01/1.22  Parsing              : 0.16
% 2.01/1.22  CNF conversion       : 0.02
% 2.01/1.22  Main loop            : 0.15
% 2.01/1.22  Inferencing          : 0.06
% 2.01/1.22  Reduction            : 0.05
% 2.01/1.22  Demodulation         : 0.03
% 2.01/1.22  BG Simplification    : 0.01
% 2.01/1.22  Subsumption          : 0.02
% 2.01/1.22  Abstraction          : 0.01
% 2.01/1.22  MUC search           : 0.00
% 2.01/1.22  Cooper               : 0.00
% 2.01/1.22  Total                : 0.48
% 2.01/1.22  Index Insertion      : 0.00
% 2.01/1.22  Index Deletion       : 0.00
% 2.01/1.22  Index Matching       : 0.00
% 2.01/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
