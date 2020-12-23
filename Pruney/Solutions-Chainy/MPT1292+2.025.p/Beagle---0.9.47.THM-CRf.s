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
% DateTime   : Thu Dec  3 10:22:32 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   52 (  63 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 ( 101 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_75,negated_conjecture,(
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

tff(f_44,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8])).

tff(c_26,plain,(
    m1_setfam_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_33,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_14])).

tff(c_60,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,k3_tarski(B_22))
      | ~ m1_setfam_1(B_22,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_63,plain,(
    ! [A_21] :
      ( r1_tarski(A_21,'#skF_4')
      | ~ m1_setfam_1('#skF_4',A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_60])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12])).

tff(c_10,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10])).

tff(c_101,plain,(
    ! [C_32,B_33,A_34] :
      ( r2_hidden(C_32,B_33)
      | ~ r2_hidden(C_32,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_2'(A_39),B_40)
      | ~ r1_tarski(A_39,B_40)
      | A_39 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_35,c_101])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_140,plain,(
    ! [B_41,A_42] :
      ( ~ r1_tarski(B_41,'#skF_2'(A_42))
      | ~ r1_tarski(A_42,B_41)
      | A_42 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_132,c_20])).

tff(c_164,plain,(
    ! [A_46] :
      ( ~ r1_tarski(A_46,'#skF_4')
      | A_46 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_34,c_140])).

tff(c_181,plain,(
    ! [A_47] :
      ( A_47 = '#skF_4'
      | ~ m1_setfam_1('#skF_4',A_47) ) ),
    inference(resolution,[status(thm)],[c_63,c_164])).

tff(c_197,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_181])).

tff(c_22,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(u1_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_204,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_22])).

tff(c_208,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36,c_204])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:00:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.97/1.21  
% 1.97/1.21  %Foreground sorts:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Background operators:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Foreground operators:
% 1.97/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.97/1.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.21  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.97/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.21  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.97/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.97/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.97/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.21  
% 1.97/1.22  tff(f_75, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 1.97/1.22  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.97/1.22  tff(f_44, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.97/1.22  tff(f_48, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.97/1.22  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.97/1.22  tff(f_41, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.97/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.97/1.22  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.97/1.22  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.97/1.22  tff(c_32, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.97/1.22  tff(c_30, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.97/1.22  tff(c_24, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.97/1.22  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.22  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8])).
% 1.97/1.22  tff(c_26, plain, (m1_setfam_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.97/1.22  tff(c_14, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.97/1.22  tff(c_33, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_14])).
% 1.97/1.22  tff(c_60, plain, (![A_21, B_22]: (r1_tarski(A_21, k3_tarski(B_22)) | ~m1_setfam_1(B_22, A_21))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.22  tff(c_63, plain, (![A_21]: (r1_tarski(A_21, '#skF_4') | ~m1_setfam_1('#skF_4', A_21))), inference(superposition, [status(thm), theory('equality')], [c_33, c_60])).
% 1.97/1.22  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.22  tff(c_34, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12])).
% 1.97/1.22  tff(c_10, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.22  tff(c_35, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10])).
% 1.97/1.22  tff(c_101, plain, (![C_32, B_33, A_34]: (r2_hidden(C_32, B_33) | ~r2_hidden(C_32, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.22  tff(c_132, plain, (![A_39, B_40]: (r2_hidden('#skF_2'(A_39), B_40) | ~r1_tarski(A_39, B_40) | A_39='#skF_4')), inference(resolution, [status(thm)], [c_35, c_101])).
% 1.97/1.22  tff(c_20, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.97/1.22  tff(c_140, plain, (![B_41, A_42]: (~r1_tarski(B_41, '#skF_2'(A_42)) | ~r1_tarski(A_42, B_41) | A_42='#skF_4')), inference(resolution, [status(thm)], [c_132, c_20])).
% 1.97/1.22  tff(c_164, plain, (![A_46]: (~r1_tarski(A_46, '#skF_4') | A_46='#skF_4')), inference(resolution, [status(thm)], [c_34, c_140])).
% 1.97/1.22  tff(c_181, plain, (![A_47]: (A_47='#skF_4' | ~m1_setfam_1('#skF_4', A_47))), inference(resolution, [status(thm)], [c_63, c_164])).
% 1.97/1.22  tff(c_197, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_26, c_181])).
% 1.97/1.22  tff(c_22, plain, (![A_13]: (~v1_xboole_0(u1_struct_0(A_13)) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.22  tff(c_204, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_197, c_22])).
% 1.97/1.22  tff(c_208, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36, c_204])).
% 1.97/1.22  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_208])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 36
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 0
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 1
% 1.97/1.22  #Demod        : 15
% 1.97/1.22  #Tautology    : 18
% 1.97/1.22  #SimpNegUnit  : 1
% 1.97/1.22  #BackRed      : 2
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.23  Preprocessing        : 0.28
% 1.97/1.23  Parsing              : 0.15
% 1.97/1.23  CNF conversion       : 0.02
% 1.97/1.23  Main loop            : 0.16
% 1.97/1.23  Inferencing          : 0.07
% 1.97/1.23  Reduction            : 0.04
% 1.97/1.23  Demodulation         : 0.03
% 1.97/1.23  BG Simplification    : 0.01
% 1.97/1.23  Subsumption          : 0.03
% 1.97/1.23  Abstraction          : 0.01
% 1.97/1.23  MUC search           : 0.00
% 1.97/1.23  Cooper               : 0.00
% 1.97/1.23  Total                : 0.47
% 1.97/1.23  Index Insertion      : 0.00
% 1.97/1.23  Index Deletion       : 0.00
% 1.97/1.23  Index Matching       : 0.00
% 1.97/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
