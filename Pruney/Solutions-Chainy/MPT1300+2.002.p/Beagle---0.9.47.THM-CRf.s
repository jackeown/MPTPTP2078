%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:44 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.42s
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
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( ( r1_tarski(B,C)
                    & v1_tops_2(C,A) )
                 => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_30,plain,(
    ~ v1_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    v1_tops_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_9,B_15] :
      ( m1_subset_1('#skF_3'(A_9,B_15),k1_zfmisc_1(u1_struct_0(A_9)))
      | v1_tops_2(B_15,A_9)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_3'(A_35,B_36),B_36)
      | v1_tops_2(B_36,A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35))))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v1_tops_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_81,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v1_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_75])).

tff(c_82,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_81])).

tff(c_34,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_41,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_45,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_41])).

tff(c_50,plain,(
    ! [D_25,A_26,B_27] :
      ( ~ r2_hidden(D_25,A_26)
      | r2_hidden(D_25,k2_xboole_0(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_53,plain,(
    ! [D_25] :
      ( ~ r2_hidden(D_25,'#skF_5')
      | r2_hidden(D_25,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_50])).

tff(c_86,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_53])).

tff(c_542,plain,(
    ! [C_77,A_78,B_79] :
      ( v3_pre_topc(C_77,A_78)
      | ~ r2_hidden(C_77,B_79)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v1_tops_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78))))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4535,plain,(
    ! [A_205] :
      ( v3_pre_topc('#skF_3'('#skF_4','#skF_5'),A_205)
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ v1_tops_2('#skF_6',A_205)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_205))))
      | ~ l1_pre_topc(A_205) ) ),
    inference(resolution,[status(thm)],[c_86,c_542])).

tff(c_4539,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_tops_2('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | v1_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_4535])).

tff(c_4542,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_32,c_4539])).

tff(c_4543,plain,(
    v3_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4542])).

tff(c_24,plain,(
    ! [A_9,B_15] :
      ( ~ v3_pre_topc('#skF_3'(A_9,B_15),A_9)
      | v1_tops_2(B_15,A_9)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4545,plain,
    ( v1_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4543,c_24])).

tff(c_4548,plain,(
    v1_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_4545])).

tff(c_4550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.14  
% 5.42/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.14  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.42/2.14  
% 5.42/2.14  %Foreground sorts:
% 5.42/2.14  
% 5.42/2.14  
% 5.42/2.14  %Background operators:
% 5.42/2.14  
% 5.42/2.14  
% 5.42/2.14  %Foreground operators:
% 5.42/2.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.42/2.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.42/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.42/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.42/2.14  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 5.42/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.42/2.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.42/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.42/2.14  tff('#skF_5', type, '#skF_5': $i).
% 5.42/2.14  tff('#skF_6', type, '#skF_6': $i).
% 5.42/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.42/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.42/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.42/2.14  tff('#skF_4', type, '#skF_4': $i).
% 5.42/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.42/2.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.42/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.42/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.42/2.14  
% 5.42/2.15  tff(f_67, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 5.42/2.15  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 5.42/2.15  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.42/2.15  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.42/2.15  tff(c_30, plain, (~v1_tops_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.42/2.15  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.42/2.15  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.42/2.15  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.42/2.15  tff(c_32, plain, (v1_tops_2('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.42/2.15  tff(c_28, plain, (![A_9, B_15]: (m1_subset_1('#skF_3'(A_9, B_15), k1_zfmisc_1(u1_struct_0(A_9))) | v1_tops_2(B_15, A_9) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.42/2.15  tff(c_71, plain, (![A_35, B_36]: (r2_hidden('#skF_3'(A_35, B_36), B_36) | v1_tops_2(B_36, A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35)))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.42/2.15  tff(c_75, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v1_tops_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_38, c_71])).
% 5.42/2.15  tff(c_81, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v1_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_75])).
% 5.42/2.15  tff(c_82, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_30, c_81])).
% 5.42/2.15  tff(c_34, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.42/2.15  tff(c_41, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.42/2.15  tff(c_45, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_34, c_41])).
% 5.42/2.15  tff(c_50, plain, (![D_25, A_26, B_27]: (~r2_hidden(D_25, A_26) | r2_hidden(D_25, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.42/2.15  tff(c_53, plain, (![D_25]: (~r2_hidden(D_25, '#skF_5') | r2_hidden(D_25, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_50])).
% 5.42/2.15  tff(c_86, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_82, c_53])).
% 5.42/2.15  tff(c_542, plain, (![C_77, A_78, B_79]: (v3_pre_topc(C_77, A_78) | ~r2_hidden(C_77, B_79) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~v1_tops_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78)))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.42/2.15  tff(c_4535, plain, (![A_205]: (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), A_205) | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0(A_205))) | ~v1_tops_2('#skF_6', A_205) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_205)))) | ~l1_pre_topc(A_205))), inference(resolution, [status(thm)], [c_86, c_542])).
% 5.42/2.15  tff(c_4539, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v1_tops_2('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | v1_tops_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_4535])).
% 5.42/2.15  tff(c_4542, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_32, c_4539])).
% 5.42/2.15  tff(c_4543, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_4542])).
% 5.42/2.15  tff(c_24, plain, (![A_9, B_15]: (~v3_pre_topc('#skF_3'(A_9, B_15), A_9) | v1_tops_2(B_15, A_9) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.42/2.15  tff(c_4545, plain, (v1_tops_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4543, c_24])).
% 5.42/2.15  tff(c_4548, plain, (v1_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_4545])).
% 5.42/2.15  tff(c_4550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_4548])).
% 5.42/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.15  
% 5.42/2.15  Inference rules
% 5.42/2.15  ----------------------
% 5.42/2.15  #Ref     : 0
% 5.42/2.15  #Sup     : 893
% 5.42/2.15  #Fact    : 28
% 5.42/2.15  #Define  : 0
% 5.42/2.15  #Split   : 4
% 5.42/2.15  #Chain   : 0
% 5.42/2.15  #Close   : 0
% 5.42/2.15  
% 5.42/2.15  Ordering : KBO
% 5.42/2.15  
% 5.42/2.15  Simplification rules
% 5.42/2.15  ----------------------
% 5.42/2.15  #Subsume      : 375
% 5.42/2.15  #Demod        : 1149
% 5.42/2.15  #Tautology    : 245
% 5.42/2.15  #SimpNegUnit  : 25
% 5.42/2.15  #BackRed      : 16
% 5.42/2.15  
% 5.42/2.15  #Partial instantiations: 0
% 5.42/2.15  #Strategies tried      : 1
% 5.42/2.15  
% 5.42/2.15  Timing (in seconds)
% 5.42/2.15  ----------------------
% 5.42/2.15  Preprocessing        : 0.25
% 5.42/2.15  Parsing              : 0.13
% 5.42/2.15  CNF conversion       : 0.02
% 5.42/2.15  Main loop            : 1.03
% 5.42/2.15  Inferencing          : 0.34
% 5.42/2.15  Reduction            : 0.34
% 5.42/2.15  Demodulation         : 0.25
% 5.42/2.15  BG Simplification    : 0.03
% 5.42/2.15  Subsumption          : 0.26
% 5.42/2.15  Abstraction          : 0.05
% 5.42/2.15  MUC search           : 0.00
% 5.42/2.15  Cooper               : 0.00
% 5.42/2.15  Total                : 1.30
% 5.42/2.15  Index Insertion      : 0.00
% 5.42/2.15  Index Deletion       : 0.00
% 5.42/2.15  Index Matching       : 0.00
% 5.42/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
