%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:34 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 107 expanded)
%              Number of leaves         :   27 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :   71 ( 177 expanded)
%              Number of equality atoms :   16 (  41 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > k4_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_40,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2])).

tff(c_28,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_37,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | A_14 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_38,plain,(
    ! [A_1] : m1_subset_1('#skF_3',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_74,plain,(
    ! [A_46,B_47] :
      ( k5_setfam_1(A_46,B_47) = k3_tarski(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_79,plain,(
    ! [A_46] : k5_setfam_1(A_46,'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_87,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k5_setfam_1(A_49,B_50),k1_zfmisc_1(A_49))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_46] :
      ( m1_subset_1(k3_tarski('#skF_3'),k1_zfmisc_1(A_46))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_87])).

tff(c_104,plain,(
    ! [A_51] : m1_subset_1(k3_tarski('#skF_3'),k1_zfmisc_1(A_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_98])).

tff(c_12,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_115,plain,(
    ! [A_51,A_9] :
      ( ~ v1_xboole_0(A_51)
      | ~ r2_hidden(A_9,k3_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_117,plain,(
    ! [A_52] : ~ r2_hidden(A_52,k3_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_122,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_37,c_117])).

tff(c_125,plain,(
    ! [A_46] : k5_setfam_1(A_46,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_79])).

tff(c_159,plain,(
    ! [A_57,B_58] :
      ( k5_setfam_1(A_57,B_58) = A_57
      | ~ m1_setfam_1(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_167,plain,(
    ! [A_57] :
      ( k5_setfam_1(A_57,'#skF_3') = A_57
      | ~ m1_setfam_1('#skF_3',A_57) ) ),
    inference(resolution,[status(thm)],[c_38,c_159])).

tff(c_171,plain,(
    ! [A_59] :
      ( A_59 = '#skF_3'
      | ~ m1_setfam_1('#skF_3',A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_167])).

tff(c_179,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_171])).

tff(c_24,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_185,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_24])).

tff(c_189,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40,c_185])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_189])).

tff(c_192,plain,(
    ! [A_51] : ~ v1_xboole_0(A_51) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.23  %$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > k4_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.10/1.23  
% 2.10/1.23  %Foreground sorts:
% 2.10/1.23  
% 2.10/1.23  
% 2.10/1.23  %Background operators:
% 2.10/1.23  
% 2.10/1.23  
% 2.10/1.23  %Foreground operators:
% 2.10/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.23  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.10/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.10/1.23  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.10/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.23  
% 2.10/1.24  tff(f_93, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 2.10/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.10/1.24  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.10/1.24  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.10/1.24  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.10/1.24  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.10/1.24  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.10/1.24  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.10/1.24  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.10/1.24  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.24  tff(c_32, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.24  tff(c_26, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.10/1.24  tff(c_40, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2])).
% 2.10/1.24  tff(c_28, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.10/1.24  tff(c_18, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.24  tff(c_37, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | A_14='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_18])).
% 2.10/1.24  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.10/1.24  tff(c_38, plain, (![A_1]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4])).
% 2.10/1.24  tff(c_74, plain, (![A_46, B_47]: (k5_setfam_1(A_46, B_47)=k3_tarski(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.10/1.24  tff(c_79, plain, (![A_46]: (k5_setfam_1(A_46, '#skF_3')=k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_74])).
% 2.10/1.24  tff(c_87, plain, (![A_49, B_50]: (m1_subset_1(k5_setfam_1(A_49, B_50), k1_zfmisc_1(A_49)) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.24  tff(c_98, plain, (![A_46]: (m1_subset_1(k3_tarski('#skF_3'), k1_zfmisc_1(A_46)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(superposition, [status(thm), theory('equality')], [c_79, c_87])).
% 2.10/1.24  tff(c_104, plain, (![A_51]: (m1_subset_1(k3_tarski('#skF_3'), k1_zfmisc_1(A_51)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_98])).
% 2.10/1.24  tff(c_12, plain, (![C_11, B_10, A_9]: (~v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.24  tff(c_115, plain, (![A_51, A_9]: (~v1_xboole_0(A_51) | ~r2_hidden(A_9, k3_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_104, c_12])).
% 2.10/1.24  tff(c_117, plain, (![A_52]: (~r2_hidden(A_52, k3_tarski('#skF_3')))), inference(splitLeft, [status(thm)], [c_115])).
% 2.10/1.24  tff(c_122, plain, (k3_tarski('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_37, c_117])).
% 2.10/1.24  tff(c_125, plain, (![A_46]: (k5_setfam_1(A_46, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_79])).
% 2.10/1.24  tff(c_159, plain, (![A_57, B_58]: (k5_setfam_1(A_57, B_58)=A_57 | ~m1_setfam_1(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.24  tff(c_167, plain, (![A_57]: (k5_setfam_1(A_57, '#skF_3')=A_57 | ~m1_setfam_1('#skF_3', A_57))), inference(resolution, [status(thm)], [c_38, c_159])).
% 2.10/1.24  tff(c_171, plain, (![A_59]: (A_59='#skF_3' | ~m1_setfam_1('#skF_3', A_59))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_167])).
% 2.10/1.24  tff(c_179, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_171])).
% 2.10/1.24  tff(c_24, plain, (![A_24]: (~v1_xboole_0(u1_struct_0(A_24)) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.24  tff(c_185, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_179, c_24])).
% 2.10/1.24  tff(c_189, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40, c_185])).
% 2.10/1.24  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_189])).
% 2.10/1.24  tff(c_192, plain, (![A_51]: (~v1_xboole_0(A_51))), inference(splitRight, [status(thm)], [c_115])).
% 2.10/1.24  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_40])).
% 2.10/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  Inference rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Ref     : 0
% 2.10/1.24  #Sup     : 32
% 2.10/1.24  #Fact    : 0
% 2.10/1.24  #Define  : 0
% 2.10/1.24  #Split   : 2
% 2.10/1.24  #Chain   : 0
% 2.10/1.24  #Close   : 0
% 2.10/1.24  
% 2.10/1.24  Ordering : KBO
% 2.10/1.24  
% 2.10/1.24  Simplification rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Subsume      : 5
% 2.10/1.24  #Demod        : 24
% 2.10/1.24  #Tautology    : 16
% 2.10/1.24  #SimpNegUnit  : 2
% 2.10/1.24  #BackRed      : 5
% 2.10/1.24  
% 2.10/1.24  #Partial instantiations: 0
% 2.10/1.24  #Strategies tried      : 1
% 2.10/1.24  
% 2.10/1.24  Timing (in seconds)
% 2.10/1.24  ----------------------
% 2.28/1.24  Preprocessing        : 0.29
% 2.28/1.24  Parsing              : 0.16
% 2.28/1.24  CNF conversion       : 0.02
% 2.28/1.24  Main loop            : 0.16
% 2.28/1.24  Inferencing          : 0.06
% 2.28/1.24  Reduction            : 0.05
% 2.28/1.24  Demodulation         : 0.03
% 2.28/1.24  BG Simplification    : 0.01
% 2.28/1.24  Subsumption          : 0.02
% 2.28/1.24  Abstraction          : 0.01
% 2.28/1.24  MUC search           : 0.00
% 2.28/1.24  Cooper               : 0.00
% 2.28/1.25  Total                : 0.48
% 2.28/1.25  Index Insertion      : 0.00
% 2.28/1.25  Index Deletion       : 0.00
% 2.28/1.25  Index Matching       : 0.00
% 2.28/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
