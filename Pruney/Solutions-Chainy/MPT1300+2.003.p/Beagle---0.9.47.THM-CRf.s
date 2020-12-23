%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:44 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :   47 (  67 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 165 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( ( r1_tarski(B,C)
                    & v1_tops_2(C,A) )
                 => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_32,plain,(
    ~ v1_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    v1_tops_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    ! [A_12,B_18] :
      ( m1_subset_1('#skF_3'(A_12,B_18),k1_zfmisc_1(u1_struct_0(A_12)))
      | v1_tops_2(B_18,A_12)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12))))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_3'(A_53,B_54),B_54)
      | v1_tops_2(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v1_tops_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_102])).

tff(c_112,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v1_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_106])).

tff(c_113,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_112])).

tff(c_36,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_43,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_43])).

tff(c_52,plain,(
    ! [D_28,B_29,A_30] :
      ( r2_hidden(D_28,B_29)
      | ~ r2_hidden(D_28,k3_xboole_0(A_30,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_55,plain,(
    ! [D_28] :
      ( r2_hidden(D_28,'#skF_6')
      | ~ r2_hidden(D_28,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_52])).

tff(c_123,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_55])).

tff(c_535,plain,(
    ! [C_108,A_109,B_110] :
      ( v3_pre_topc(C_108,A_109)
      | ~ r2_hidden(C_108,B_110)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ v1_tops_2(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_109))))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6028,plain,(
    ! [A_459] :
      ( v3_pre_topc('#skF_3'('#skF_4','#skF_5'),A_459)
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0(A_459)))
      | ~ v1_tops_2('#skF_6',A_459)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_459))))
      | ~ l1_pre_topc(A_459) ) ),
    inference(resolution,[status(thm)],[c_123,c_535])).

tff(c_6032,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_tops_2('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v1_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_6028])).

tff(c_6043,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_34,c_6032])).

tff(c_6044,plain,(
    v3_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6043])).

tff(c_26,plain,(
    ! [A_12,B_18] :
      ( ~ v3_pre_topc('#skF_3'(A_12,B_18),A_12)
      | v1_tops_2(B_18,A_12)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12))))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6052,plain,
    ( v1_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6044,c_26])).

tff(c_6055,plain,(
    v1_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_6052])).

tff(c_6057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 16:27:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.97/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.81  
% 7.97/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.81  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 7.97/2.81  
% 7.97/2.81  %Foreground sorts:
% 7.97/2.81  
% 7.97/2.81  
% 7.97/2.81  %Background operators:
% 7.97/2.81  
% 7.97/2.81  
% 7.97/2.81  %Foreground operators:
% 7.97/2.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.97/2.81  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.97/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.97/2.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.97/2.81  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 7.97/2.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.97/2.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.97/2.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.97/2.81  tff('#skF_5', type, '#skF_5': $i).
% 7.97/2.81  tff('#skF_6', type, '#skF_6': $i).
% 7.97/2.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.97/2.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.97/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.97/2.81  tff('#skF_4', type, '#skF_4': $i).
% 7.97/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.97/2.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.97/2.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.97/2.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.97/2.81  
% 7.97/2.82  tff(f_73, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tops_2)).
% 7.97/2.82  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 7.97/2.82  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.97/2.82  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.97/2.82  tff(c_32, plain, (~v1_tops_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.97/2.82  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.97/2.82  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.97/2.82  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.97/2.82  tff(c_34, plain, (v1_tops_2('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.97/2.82  tff(c_30, plain, (![A_12, B_18]: (m1_subset_1('#skF_3'(A_12, B_18), k1_zfmisc_1(u1_struct_0(A_12))) | v1_tops_2(B_18, A_12) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12)))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.97/2.82  tff(c_102, plain, (![A_53, B_54]: (r2_hidden('#skF_3'(A_53, B_54), B_54) | v1_tops_2(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.97/2.82  tff(c_106, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v1_tops_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_102])).
% 7.97/2.82  tff(c_112, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v1_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_106])).
% 7.97/2.82  tff(c_113, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_32, c_112])).
% 7.97/2.82  tff(c_36, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.97/2.82  tff(c_43, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.97/2.82  tff(c_47, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_36, c_43])).
% 7.97/2.82  tff(c_52, plain, (![D_28, B_29, A_30]: (r2_hidden(D_28, B_29) | ~r2_hidden(D_28, k3_xboole_0(A_30, B_29)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.97/2.82  tff(c_55, plain, (![D_28]: (r2_hidden(D_28, '#skF_6') | ~r2_hidden(D_28, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_52])).
% 7.97/2.82  tff(c_123, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_55])).
% 7.97/2.82  tff(c_535, plain, (![C_108, A_109, B_110]: (v3_pre_topc(C_108, A_109) | ~r2_hidden(C_108, B_110) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~v1_tops_2(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_109)))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.97/2.82  tff(c_6028, plain, (![A_459]: (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), A_459) | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0(A_459))) | ~v1_tops_2('#skF_6', A_459) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_459)))) | ~l1_pre_topc(A_459))), inference(resolution, [status(thm)], [c_123, c_535])).
% 7.97/2.82  tff(c_6032, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v1_tops_2('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | v1_tops_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_6028])).
% 7.97/2.82  tff(c_6043, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_34, c_6032])).
% 7.97/2.82  tff(c_6044, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_6043])).
% 7.97/2.82  tff(c_26, plain, (![A_12, B_18]: (~v3_pre_topc('#skF_3'(A_12, B_18), A_12) | v1_tops_2(B_18, A_12) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12)))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.97/2.82  tff(c_6052, plain, (v1_tops_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6044, c_26])).
% 7.97/2.82  tff(c_6055, plain, (v1_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_6052])).
% 7.97/2.82  tff(c_6057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_6055])).
% 7.97/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.82  
% 7.97/2.82  Inference rules
% 7.97/2.82  ----------------------
% 7.97/2.82  #Ref     : 0
% 7.97/2.82  #Sup     : 1408
% 7.97/2.82  #Fact    : 0
% 7.97/2.82  #Define  : 0
% 7.97/2.82  #Split   : 7
% 7.97/2.82  #Chain   : 0
% 7.97/2.82  #Close   : 0
% 7.97/2.82  
% 7.97/2.82  Ordering : KBO
% 7.97/2.82  
% 7.97/2.82  Simplification rules
% 7.97/2.82  ----------------------
% 7.97/2.82  #Subsume      : 606
% 7.97/2.82  #Demod        : 1162
% 7.97/2.82  #Tautology    : 101
% 7.97/2.82  #SimpNegUnit  : 5
% 7.97/2.82  #BackRed      : 0
% 7.97/2.82  
% 7.97/2.82  #Partial instantiations: 0
% 7.97/2.82  #Strategies tried      : 1
% 7.97/2.82  
% 7.97/2.82  Timing (in seconds)
% 7.97/2.82  ----------------------
% 7.97/2.82  Preprocessing        : 0.29
% 7.97/2.82  Parsing              : 0.15
% 7.97/2.82  CNF conversion       : 0.03
% 7.97/2.82  Main loop            : 1.71
% 7.97/2.82  Inferencing          : 0.57
% 7.97/2.82  Reduction            : 0.45
% 7.97/2.82  Demodulation         : 0.30
% 7.97/2.82  BG Simplification    : 0.05
% 7.97/2.82  Subsumption          : 0.53
% 7.97/2.82  Abstraction          : 0.10
% 7.97/2.82  MUC search           : 0.00
% 7.97/2.82  Cooper               : 0.00
% 7.97/2.82  Total                : 2.02
% 7.97/2.82  Index Insertion      : 0.00
% 8.15/2.82  Index Deletion       : 0.00
% 8.15/2.82  Index Matching       : 0.00
% 8.15/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
