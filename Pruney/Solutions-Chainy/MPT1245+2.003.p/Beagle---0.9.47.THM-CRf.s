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
% DateTime   : Thu Dec  3 10:20:50 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   40 (  77 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 160 expanded)
%              Number of equality atoms :   10 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,B))) = k2_pre_topc(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k1_tops_1(A,B)) = k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,k1_tops_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).

tff(c_14,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) != k2_pre_topc('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k1_tops_1(A_20,B_21),B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_30])).

tff(c_35,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_32])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_35,c_2])).

tff(c_39,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_16,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [B_24,A_25,C_26] :
      ( r1_tarski(B_24,k1_tops_1(A_25,C_26))
      | ~ r1_tarski(B_24,C_26)
      | ~ v3_pre_topc(B_24,A_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_59,plain,(
    ! [B_24] :
      ( r1_tarski(B_24,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_24,'#skF_2')
      | ~ v3_pre_topc(B_24,'#skF_1')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_57])).

tff(c_63,plain,(
    ! [B_27] :
      ( r1_tarski(B_27,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_27,'#skF_2')
      | ~ v3_pre_topc(B_27,'#skF_1')
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_66,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_69,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6,c_66])).

tff(c_71,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_69])).

tff(c_72,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_81,plain,(
    ! [A_28,B_29] :
      ( k2_pre_topc(A_28,k1_tops_1(A_28,k2_pre_topc(A_28,k1_tops_1(A_28,B_29)))) = k2_pre_topc(A_28,k1_tops_1(A_28,B_29))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_96,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_81])).

tff(c_102,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_72,c_96])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:24:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.10  
% 1.71/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.11  %$ v3_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.71/1.11  
% 1.71/1.11  %Foreground sorts:
% 1.71/1.11  
% 1.71/1.11  
% 1.71/1.11  %Background operators:
% 1.71/1.11  
% 1.71/1.11  
% 1.71/1.11  %Foreground operators:
% 1.71/1.11  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.71/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.11  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.71/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.71/1.11  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 1.71/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.11  
% 1.71/1.12  tff(f_69, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, B))) = k2_pre_topc(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tops_1)).
% 1.71/1.12  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 1.71/1.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.71/1.12  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 1.71/1.12  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k1_tops_1(A, B)) = k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tops_1)).
% 1.71/1.12  tff(c_14, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))!=k2_pre_topc('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.71/1.12  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.71/1.12  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.71/1.12  tff(c_30, plain, (![A_20, B_21]: (r1_tarski(k1_tops_1(A_20, B_21), B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.71/1.12  tff(c_32, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_30])).
% 1.71/1.12  tff(c_35, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_32])).
% 1.71/1.12  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.12  tff(c_38, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_35, c_2])).
% 1.71/1.12  tff(c_39, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 1.71/1.12  tff(c_16, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.71/1.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.12  tff(c_57, plain, (![B_24, A_25, C_26]: (r1_tarski(B_24, k1_tops_1(A_25, C_26)) | ~r1_tarski(B_24, C_26) | ~v3_pre_topc(B_24, A_25) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.71/1.12  tff(c_59, plain, (![B_24]: (r1_tarski(B_24, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_24, '#skF_2') | ~v3_pre_topc(B_24, '#skF_1') | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_57])).
% 1.71/1.12  tff(c_63, plain, (![B_27]: (r1_tarski(B_27, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_27, '#skF_2') | ~v3_pre_topc(B_27, '#skF_1') | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_59])).
% 1.71/1.12  tff(c_66, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_63])).
% 1.71/1.12  tff(c_69, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6, c_66])).
% 1.71/1.12  tff(c_71, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_69])).
% 1.71/1.12  tff(c_72, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 1.71/1.12  tff(c_81, plain, (![A_28, B_29]: (k2_pre_topc(A_28, k1_tops_1(A_28, k2_pre_topc(A_28, k1_tops_1(A_28, B_29))))=k2_pre_topc(A_28, k1_tops_1(A_28, B_29)) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.71/1.12  tff(c_96, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_72, c_81])).
% 1.71/1.12  tff(c_102, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_72, c_96])).
% 1.71/1.12  tff(c_104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_102])).
% 1.71/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.12  
% 1.71/1.12  Inference rules
% 1.71/1.12  ----------------------
% 1.71/1.12  #Ref     : 0
% 1.71/1.12  #Sup     : 16
% 1.71/1.12  #Fact    : 0
% 1.71/1.12  #Define  : 0
% 1.71/1.12  #Split   : 1
% 1.71/1.12  #Chain   : 0
% 1.71/1.12  #Close   : 0
% 1.71/1.12  
% 1.71/1.12  Ordering : KBO
% 1.71/1.12  
% 1.71/1.12  Simplification rules
% 1.71/1.12  ----------------------
% 1.71/1.12  #Subsume      : 0
% 1.71/1.12  #Demod        : 13
% 1.71/1.12  #Tautology    : 14
% 1.71/1.12  #SimpNegUnit  : 2
% 1.71/1.12  #BackRed      : 1
% 1.71/1.12  
% 1.71/1.12  #Partial instantiations: 0
% 1.71/1.12  #Strategies tried      : 1
% 1.71/1.12  
% 1.71/1.12  Timing (in seconds)
% 1.71/1.12  ----------------------
% 1.71/1.12  Preprocessing        : 0.27
% 1.71/1.12  Parsing              : 0.15
% 1.71/1.12  CNF conversion       : 0.02
% 1.71/1.12  Main loop            : 0.12
% 1.71/1.12  Inferencing          : 0.04
% 1.71/1.12  Reduction            : 0.04
% 1.71/1.12  Demodulation         : 0.03
% 1.71/1.12  BG Simplification    : 0.01
% 1.71/1.12  Subsumption          : 0.03
% 1.71/1.12  Abstraction          : 0.01
% 1.71/1.13  MUC search           : 0.00
% 1.71/1.13  Cooper               : 0.00
% 1.71/1.13  Total                : 0.42
% 1.71/1.13  Index Insertion      : 0.00
% 1.71/1.13  Index Deletion       : 0.00
% 1.71/1.13  Index Matching       : 0.00
% 1.71/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
