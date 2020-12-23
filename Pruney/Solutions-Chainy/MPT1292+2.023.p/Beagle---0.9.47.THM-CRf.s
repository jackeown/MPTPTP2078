%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:32 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 105 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_41,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8])).

tff(c_30,plain,(
    m1_setfam_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_37,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_20])).

tff(c_93,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,k3_tarski(B_26))
      | ~ m1_setfam_1(B_26,A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_99,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,'#skF_4')
      | ~ m1_setfam_1('#skF_4',A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_93])).

tff(c_10,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10])).

tff(c_154,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_167,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_2'(A_42),B_43)
      | ~ r1_tarski(A_42,B_43)
      | A_42 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_41,c_154])).

tff(c_14,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_14])).

tff(c_73,plain,(
    ! [A_18,B_19] : ~ r2_hidden(A_18,k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [A_8] : ~ r2_hidden(A_8,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_73])).

tff(c_191,plain,(
    ! [A_46] :
      ( ~ r1_tarski(A_46,'#skF_4')
      | A_46 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_167,c_79])).

tff(c_208,plain,(
    ! [A_47] :
      ( A_47 = '#skF_4'
      | ~ m1_setfam_1('#skF_4',A_47) ) ),
    inference(resolution,[status(thm)],[c_99,c_191])).

tff(c_224,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_208])).

tff(c_26,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_231,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_26])).

tff(c_235,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42,c_231])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:16:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.26  
% 2.01/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.26  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.01/1.26  
% 2.01/1.26  %Foreground sorts:
% 2.01/1.26  
% 2.01/1.26  
% 2.01/1.26  %Background operators:
% 2.01/1.26  
% 2.01/1.26  
% 2.01/1.26  %Foreground operators:
% 2.01/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.01/1.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.26  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.01/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.01/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.01/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.01/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.26  
% 2.01/1.27  tff(f_77, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 2.01/1.27  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.01/1.27  tff(f_51, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.01/1.27  tff(f_55, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.01/1.27  tff(f_41, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.01/1.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.01/1.27  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.01/1.27  tff(f_50, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.01/1.27  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.01/1.27  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.01/1.27  tff(c_34, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.01/1.27  tff(c_28, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.01/1.27  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.01/1.27  tff(c_42, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8])).
% 2.01/1.27  tff(c_30, plain, (m1_setfam_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.01/1.27  tff(c_20, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.01/1.27  tff(c_37, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_20])).
% 2.01/1.27  tff(c_93, plain, (![A_25, B_26]: (r1_tarski(A_25, k3_tarski(B_26)) | ~m1_setfam_1(B_26, A_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.27  tff(c_99, plain, (![A_25]: (r1_tarski(A_25, '#skF_4') | ~m1_setfam_1('#skF_4', A_25))), inference(superposition, [status(thm), theory('equality')], [c_37, c_93])).
% 2.01/1.27  tff(c_10, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.01/1.27  tff(c_41, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10])).
% 2.01/1.27  tff(c_154, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.01/1.27  tff(c_167, plain, (![A_42, B_43]: (r2_hidden('#skF_2'(A_42), B_43) | ~r1_tarski(A_42, B_43) | A_42='#skF_4')), inference(resolution, [status(thm)], [c_41, c_154])).
% 2.01/1.27  tff(c_14, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.01/1.27  tff(c_39, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_14])).
% 2.01/1.27  tff(c_73, plain, (![A_18, B_19]: (~r2_hidden(A_18, k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.01/1.27  tff(c_79, plain, (![A_8]: (~r2_hidden(A_8, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_73])).
% 2.01/1.27  tff(c_191, plain, (![A_46]: (~r1_tarski(A_46, '#skF_4') | A_46='#skF_4')), inference(resolution, [status(thm)], [c_167, c_79])).
% 2.01/1.27  tff(c_208, plain, (![A_47]: (A_47='#skF_4' | ~m1_setfam_1('#skF_4', A_47))), inference(resolution, [status(thm)], [c_99, c_191])).
% 2.01/1.27  tff(c_224, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_30, c_208])).
% 2.01/1.27  tff(c_26, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.01/1.27  tff(c_231, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_224, c_26])).
% 2.01/1.27  tff(c_235, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42, c_231])).
% 2.01/1.27  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_235])).
% 2.01/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.27  
% 2.01/1.27  Inference rules
% 2.01/1.27  ----------------------
% 2.01/1.27  #Ref     : 0
% 2.01/1.27  #Sup     : 42
% 2.01/1.27  #Fact    : 0
% 2.01/1.27  #Define  : 0
% 2.01/1.27  #Split   : 0
% 2.01/1.27  #Chain   : 0
% 2.01/1.27  #Close   : 0
% 2.01/1.27  
% 2.01/1.27  Ordering : KBO
% 2.01/1.27  
% 2.01/1.27  Simplification rules
% 2.01/1.27  ----------------------
% 2.01/1.27  #Subsume      : 2
% 2.01/1.27  #Demod        : 20
% 2.01/1.27  #Tautology    : 25
% 2.01/1.27  #SimpNegUnit  : 1
% 2.01/1.27  #BackRed      : 2
% 2.01/1.27  
% 2.01/1.27  #Partial instantiations: 0
% 2.01/1.27  #Strategies tried      : 1
% 2.01/1.27  
% 2.01/1.27  Timing (in seconds)
% 2.01/1.27  ----------------------
% 2.01/1.28  Preprocessing        : 0.28
% 2.01/1.28  Parsing              : 0.15
% 2.01/1.28  CNF conversion       : 0.02
% 2.01/1.28  Main loop            : 0.17
% 2.01/1.28  Inferencing          : 0.06
% 2.01/1.28  Reduction            : 0.05
% 2.01/1.28  Demodulation         : 0.04
% 2.01/1.28  BG Simplification    : 0.01
% 2.01/1.28  Subsumption          : 0.03
% 2.01/1.28  Abstraction          : 0.01
% 2.01/1.28  MUC search           : 0.00
% 2.01/1.28  Cooper               : 0.00
% 2.01/1.28  Total                : 0.48
% 2.01/1.28  Index Insertion      : 0.00
% 2.01/1.28  Index Deletion       : 0.00
% 2.01/1.28  Index Matching       : 0.00
% 2.01/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
