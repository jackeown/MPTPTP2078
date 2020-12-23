%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:34 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 107 expanded)
%              Number of leaves         :   27 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :   74 ( 180 expanded)
%              Number of equality atoms :   15 (  40 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_98,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

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

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_37,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2])).

tff(c_26,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_33,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | A_14 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_35,plain,(
    ! [A_1] : m1_subset_1('#skF_3',k1_zfmisc_1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4])).

tff(c_61,plain,(
    ! [A_48,B_49] :
      ( k5_setfam_1(A_48,B_49) = k3_tarski(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [A_48] : k5_setfam_1(A_48,'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_35,c_61])).

tff(c_74,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k5_setfam_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [A_48] :
      ( m1_subset_1(k3_tarski('#skF_3'),k1_zfmisc_1(A_48))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_74])).

tff(c_91,plain,(
    ! [A_53] : m1_subset_1(k3_tarski('#skF_3'),k1_zfmisc_1(A_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_85])).

tff(c_12,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_102,plain,(
    ! [A_53,A_9] :
      ( ~ v1_xboole_0(A_53)
      | ~ r2_hidden(A_9,k3_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_91,c_12])).

tff(c_104,plain,(
    ! [A_54] : ~ r2_hidden(A_54,k3_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_109,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_33,c_104])).

tff(c_129,plain,(
    ! [A_48] : k5_setfam_1(A_48,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_66])).

tff(c_152,plain,(
    ! [A_59,B_60] :
      ( k5_setfam_1(A_59,B_60) = A_59
      | ~ m1_setfam_1(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_160,plain,(
    ! [A_59] :
      ( k5_setfam_1(A_59,'#skF_3') = A_59
      | ~ m1_setfam_1('#skF_3',A_59) ) ),
    inference(resolution,[status(thm)],[c_35,c_152])).

tff(c_164,plain,(
    ! [A_61] :
      ( A_61 = '#skF_3'
      | ~ m1_setfam_1('#skF_3',A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_160])).

tff(c_172,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_164])).

tff(c_22,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_178,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_22])).

tff(c_182,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_37,c_178])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_182])).

tff(c_185,plain,(
    ! [A_53] : ~ v1_xboole_0(A_53) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n024.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:12:06 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.18  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.95/1.18  
% 1.95/1.18  %Foreground sorts:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Background operators:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Foreground operators:
% 1.95/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.95/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.95/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.18  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.95/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.95/1.18  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.95/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.18  
% 2.05/1.19  tff(f_98, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 2.05/1.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.05/1.19  tff(f_76, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.05/1.19  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.05/1.19  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.05/1.19  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.05/1.19  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.05/1.19  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.05/1.19  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.05/1.19  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.05/1.19  tff(c_30, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.05/1.19  tff(c_24, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.05/1.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.05/1.19  tff(c_37, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2])).
% 2.05/1.19  tff(c_26, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.05/1.19  tff(c_20, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.05/1.19  tff(c_33, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | A_14='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20])).
% 2.05/1.19  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.05/1.19  tff(c_35, plain, (![A_1]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4])).
% 2.05/1.19  tff(c_61, plain, (![A_48, B_49]: (k5_setfam_1(A_48, B_49)=k3_tarski(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.05/1.19  tff(c_66, plain, (![A_48]: (k5_setfam_1(A_48, '#skF_3')=k3_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_35, c_61])).
% 2.05/1.19  tff(c_74, plain, (![A_51, B_52]: (m1_subset_1(k5_setfam_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.19  tff(c_85, plain, (![A_48]: (m1_subset_1(k3_tarski('#skF_3'), k1_zfmisc_1(A_48)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(superposition, [status(thm), theory('equality')], [c_66, c_74])).
% 2.05/1.19  tff(c_91, plain, (![A_53]: (m1_subset_1(k3_tarski('#skF_3'), k1_zfmisc_1(A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_85])).
% 2.05/1.19  tff(c_12, plain, (![C_11, B_10, A_9]: (~v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.05/1.19  tff(c_102, plain, (![A_53, A_9]: (~v1_xboole_0(A_53) | ~r2_hidden(A_9, k3_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_91, c_12])).
% 2.05/1.19  tff(c_104, plain, (![A_54]: (~r2_hidden(A_54, k3_tarski('#skF_3')))), inference(splitLeft, [status(thm)], [c_102])).
% 2.05/1.19  tff(c_109, plain, (k3_tarski('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_33, c_104])).
% 2.05/1.19  tff(c_129, plain, (![A_48]: (k5_setfam_1(A_48, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_66])).
% 2.05/1.19  tff(c_152, plain, (![A_59, B_60]: (k5_setfam_1(A_59, B_60)=A_59 | ~m1_setfam_1(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.19  tff(c_160, plain, (![A_59]: (k5_setfam_1(A_59, '#skF_3')=A_59 | ~m1_setfam_1('#skF_3', A_59))), inference(resolution, [status(thm)], [c_35, c_152])).
% 2.05/1.19  tff(c_164, plain, (![A_61]: (A_61='#skF_3' | ~m1_setfam_1('#skF_3', A_61))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_160])).
% 2.05/1.19  tff(c_172, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_26, c_164])).
% 2.05/1.19  tff(c_22, plain, (![A_36]: (~v1_xboole_0(u1_struct_0(A_36)) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.05/1.19  tff(c_178, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_172, c_22])).
% 2.05/1.19  tff(c_182, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_37, c_178])).
% 2.05/1.19  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_182])).
% 2.05/1.19  tff(c_185, plain, (![A_53]: (~v1_xboole_0(A_53))), inference(splitRight, [status(thm)], [c_102])).
% 2.05/1.19  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_37])).
% 2.05/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.19  
% 2.05/1.19  Inference rules
% 2.05/1.19  ----------------------
% 2.05/1.19  #Ref     : 0
% 2.05/1.19  #Sup     : 31
% 2.05/1.19  #Fact    : 0
% 2.05/1.19  #Define  : 0
% 2.05/1.19  #Split   : 2
% 2.05/1.19  #Chain   : 0
% 2.05/1.19  #Close   : 0
% 2.05/1.19  
% 2.05/1.19  Ordering : KBO
% 2.05/1.19  
% 2.05/1.19  Simplification rules
% 2.05/1.19  ----------------------
% 2.05/1.19  #Subsume      : 5
% 2.05/1.19  #Demod        : 24
% 2.05/1.19  #Tautology    : 16
% 2.05/1.19  #SimpNegUnit  : 2
% 2.05/1.19  #BackRed      : 5
% 2.05/1.19  
% 2.05/1.19  #Partial instantiations: 0
% 2.05/1.19  #Strategies tried      : 1
% 2.05/1.19  
% 2.05/1.19  Timing (in seconds)
% 2.05/1.19  ----------------------
% 2.05/1.20  Preprocessing        : 0.32
% 2.05/1.20  Parsing              : 0.17
% 2.05/1.20  CNF conversion       : 0.02
% 2.05/1.20  Main loop            : 0.15
% 2.05/1.20  Inferencing          : 0.05
% 2.05/1.20  Reduction            : 0.05
% 2.05/1.20  Demodulation         : 0.04
% 2.05/1.20  BG Simplification    : 0.01
% 2.05/1.20  Subsumption          : 0.02
% 2.05/1.20  Abstraction          : 0.01
% 2.05/1.20  MUC search           : 0.00
% 2.05/1.20  Cooper               : 0.00
% 2.05/1.20  Total                : 0.50
% 2.05/1.20  Index Insertion      : 0.00
% 2.05/1.20  Index Deletion       : 0.00
% 2.05/1.20  Index Matching       : 0.00
% 2.05/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
