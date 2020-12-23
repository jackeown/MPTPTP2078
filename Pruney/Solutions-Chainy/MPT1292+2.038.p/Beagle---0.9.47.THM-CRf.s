%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:34 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   57 (  82 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   68 ( 127 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(f_87,negated_conjecture,(
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

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2])).

tff(c_28,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_82,plain,(
    ! [A_35,B_36] :
      ( k5_setfam_1(A_35,B_36) = k3_tarski(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    ! [A_35] : k5_setfam_1(A_35,'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_35,c_82])).

tff(c_111,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k5_setfam_1(A_43,B_44),k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_123,plain,(
    ! [A_35] :
      ( m1_subset_1(k3_tarski('#skF_3'),k1_zfmisc_1(A_35))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_111])).

tff(c_129,plain,(
    ! [A_45] : m1_subset_1(k3_tarski('#skF_3'),k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_123])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_142,plain,(
    ! [A_46] : r1_tarski(k3_tarski('#skF_3'),A_46) ),
    inference(resolution,[status(thm)],[c_129,c_12])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_45,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_1'(A_22),A_22)
      | A_22 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_49,plain,(
    ! [A_22] :
      ( ~ r1_tarski(A_22,'#skF_1'(A_22))
      | A_22 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_45,c_22])).

tff(c_152,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_142,c_49])).

tff(c_155,plain,(
    ! [A_35] : k5_setfam_1(A_35,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_92])).

tff(c_196,plain,(
    ! [A_51,B_52] :
      ( k5_setfam_1(A_51,B_52) = A_51
      | ~ m1_setfam_1(B_52,A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_208,plain,(
    ! [A_51] :
      ( k5_setfam_1(A_51,'#skF_3') = A_51
      | ~ m1_setfam_1('#skF_3',A_51) ) ),
    inference(resolution,[status(thm)],[c_35,c_196])).

tff(c_213,plain,(
    ! [A_53] :
      ( A_53 = '#skF_3'
      | ~ m1_setfam_1('#skF_3',A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_208])).

tff(c_221,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_213])).

tff(c_24,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_227,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_24])).

tff(c_231,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38,c_227])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.24  
% 2.03/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.24  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.03/1.24  
% 2.03/1.24  %Foreground sorts:
% 2.03/1.24  
% 2.03/1.24  
% 2.03/1.24  %Background operators:
% 2.03/1.24  
% 2.03/1.24  
% 2.03/1.24  %Foreground operators:
% 2.03/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.03/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.03/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.24  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.03/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.03/1.24  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.03/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.03/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.03/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.24  
% 2.03/1.25  tff(f_87, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 2.03/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.03/1.25  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.03/1.25  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.03/1.25  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.03/1.25  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.03/1.25  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.03/1.25  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.03/1.25  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.03/1.25  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.03/1.25  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.03/1.25  tff(c_32, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.03/1.25  tff(c_26, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.03/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.03/1.25  tff(c_38, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2])).
% 2.03/1.25  tff(c_28, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.03/1.25  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.03/1.25  tff(c_35, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6])).
% 2.03/1.25  tff(c_82, plain, (![A_35, B_36]: (k5_setfam_1(A_35, B_36)=k3_tarski(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.03/1.25  tff(c_92, plain, (![A_35]: (k5_setfam_1(A_35, '#skF_3')=k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_35, c_82])).
% 2.03/1.25  tff(c_111, plain, (![A_43, B_44]: (m1_subset_1(k5_setfam_1(A_43, B_44), k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_43))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.25  tff(c_123, plain, (![A_35]: (m1_subset_1(k3_tarski('#skF_3'), k1_zfmisc_1(A_35)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(superposition, [status(thm), theory('equality')], [c_92, c_111])).
% 2.03/1.25  tff(c_129, plain, (![A_45]: (m1_subset_1(k3_tarski('#skF_3'), k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_123])).
% 2.03/1.25  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.25  tff(c_142, plain, (![A_46]: (r1_tarski(k3_tarski('#skF_3'), A_46))), inference(resolution, [status(thm)], [c_129, c_12])).
% 2.03/1.25  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.03/1.25  tff(c_45, plain, (![A_22]: (r2_hidden('#skF_1'(A_22), A_22) | A_22='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4])).
% 2.03/1.25  tff(c_22, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.03/1.25  tff(c_49, plain, (![A_22]: (~r1_tarski(A_22, '#skF_1'(A_22)) | A_22='#skF_3')), inference(resolution, [status(thm)], [c_45, c_22])).
% 2.03/1.25  tff(c_152, plain, (k3_tarski('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_142, c_49])).
% 2.03/1.25  tff(c_155, plain, (![A_35]: (k5_setfam_1(A_35, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_92])).
% 2.03/1.25  tff(c_196, plain, (![A_51, B_52]: (k5_setfam_1(A_51, B_52)=A_51 | ~m1_setfam_1(B_52, A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.25  tff(c_208, plain, (![A_51]: (k5_setfam_1(A_51, '#skF_3')=A_51 | ~m1_setfam_1('#skF_3', A_51))), inference(resolution, [status(thm)], [c_35, c_196])).
% 2.03/1.25  tff(c_213, plain, (![A_53]: (A_53='#skF_3' | ~m1_setfam_1('#skF_3', A_53))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_208])).
% 2.03/1.25  tff(c_221, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_213])).
% 2.03/1.25  tff(c_24, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.03/1.25  tff(c_227, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_221, c_24])).
% 2.03/1.25  tff(c_231, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38, c_227])).
% 2.03/1.25  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_231])).
% 2.03/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  Inference rules
% 2.03/1.25  ----------------------
% 2.03/1.25  #Ref     : 0
% 2.03/1.25  #Sup     : 40
% 2.03/1.25  #Fact    : 0
% 2.03/1.25  #Define  : 0
% 2.03/1.25  #Split   : 0
% 2.03/1.25  #Chain   : 0
% 2.03/1.25  #Close   : 0
% 2.03/1.25  
% 2.03/1.25  Ordering : KBO
% 2.03/1.25  
% 2.03/1.25  Simplification rules
% 2.03/1.25  ----------------------
% 2.03/1.25  #Subsume      : 1
% 2.03/1.25  #Demod        : 28
% 2.03/1.25  #Tautology    : 21
% 2.03/1.25  #SimpNegUnit  : 1
% 2.03/1.25  #BackRed      : 4
% 2.03/1.25  
% 2.03/1.25  #Partial instantiations: 0
% 2.03/1.25  #Strategies tried      : 1
% 2.03/1.25  
% 2.03/1.25  Timing (in seconds)
% 2.03/1.25  ----------------------
% 2.03/1.26  Preprocessing        : 0.32
% 2.03/1.26  Parsing              : 0.17
% 2.03/1.26  CNF conversion       : 0.02
% 2.03/1.26  Main loop            : 0.17
% 2.03/1.26  Inferencing          : 0.07
% 2.03/1.26  Reduction            : 0.05
% 2.03/1.26  Demodulation         : 0.04
% 2.03/1.26  BG Simplification    : 0.01
% 2.03/1.26  Subsumption          : 0.02
% 2.03/1.26  Abstraction          : 0.01
% 2.03/1.26  MUC search           : 0.00
% 2.03/1.26  Cooper               : 0.00
% 2.03/1.26  Total                : 0.52
% 2.03/1.26  Index Insertion      : 0.00
% 2.03/1.26  Index Deletion       : 0.00
% 2.03/1.26  Index Matching       : 0.00
% 2.03/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
