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
% DateTime   : Thu Dec  3 10:22:50 EST 2020

% Result     : Theorem 6.70s
% Output     : CNFRefutation 6.99s
% Verified   : 
% Statistics : Number of formulae       :   49 (  76 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 130 expanded)
%              Number of equality atoms :    7 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_95,plain,(
    ! [A_47,B_48,C_49] :
      ( k7_subset_1(A_47,B_48,C_49) = k4_xboole_0(B_48,C_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_230,plain,(
    ! [C_68] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_68) = k4_xboole_0('#skF_2',C_68) ),
    inference(resolution,[status(thm)],[c_26,c_95])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k7_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_239,plain,(
    ! [C_68] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_68),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_10])).

tff(c_247,plain,(
    ! [C_68] : m1_subset_1(k4_xboole_0('#skF_2',C_68),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_239])).

tff(c_6,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_29,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_110,plain,(
    ! [A_7,C_49] : k7_subset_1(A_7,A_7,C_49) = k4_xboole_0(A_7,C_49) ),
    inference(resolution,[status(thm)],[c_29,c_95])).

tff(c_82,plain,(
    ! [A_40,B_41,C_42] :
      ( m1_subset_1(k7_subset_1(A_40,B_41,C_42),k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(k7_subset_1(A_40,B_41,C_42),A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_82,c_14])).

tff(c_175,plain,(
    ! [B_59,A_60,C_61] :
      ( v1_tops_2(B_59,A_60)
      | ~ v1_tops_2(C_61,A_60)
      | ~ r1_tarski(B_59,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60))))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60))))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1942,plain,(
    ! [A_212,B_213,C_214,A_215] :
      ( v1_tops_2(k7_subset_1(A_212,B_213,C_214),A_215)
      | ~ v1_tops_2(A_212,A_215)
      | ~ m1_subset_1(A_212,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215))))
      | ~ m1_subset_1(k7_subset_1(A_212,B_213,C_214),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215))))
      | ~ l1_pre_topc(A_215)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(A_212)) ) ),
    inference(resolution,[status(thm)],[c_86,c_175])).

tff(c_1972,plain,(
    ! [A_7,C_49,A_215] :
      ( v1_tops_2(k7_subset_1(A_7,A_7,C_49),A_215)
      | ~ v1_tops_2(A_7,A_215)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215))))
      | ~ m1_subset_1(k4_xboole_0(A_7,C_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215))))
      | ~ l1_pre_topc(A_215)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_1942])).

tff(c_6511,plain,(
    ! [A_511,C_512,A_513] :
      ( v1_tops_2(k4_xboole_0(A_511,C_512),A_513)
      | ~ v1_tops_2(A_511,A_513)
      | ~ m1_subset_1(A_511,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_513))))
      | ~ m1_subset_1(k4_xboole_0(A_511,C_512),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_513))))
      | ~ l1_pre_topc(A_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_110,c_1972])).

tff(c_6558,plain,(
    ! [C_68] :
      ( v1_tops_2(k4_xboole_0('#skF_2',C_68),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_247,c_6511])).

tff(c_6608,plain,(
    ! [C_68] : v1_tops_2(k4_xboole_0('#skF_2',C_68),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_6558])).

tff(c_109,plain,(
    ! [C_49] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_49) = k4_xboole_0('#skF_2',C_49) ),
    inference(resolution,[status(thm)],[c_26,c_95])).

tff(c_20,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_229,plain,(
    ~ v1_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_20])).

tff(c_6618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6608,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.70/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.47  
% 6.70/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.47  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.70/2.47  
% 6.70/2.47  %Foreground sorts:
% 6.70/2.47  
% 6.70/2.47  
% 6.70/2.47  %Background operators:
% 6.70/2.47  
% 6.70/2.47  
% 6.70/2.47  %Foreground operators:
% 6.70/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.70/2.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.70/2.47  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 6.70/2.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.70/2.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.70/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.70/2.47  tff('#skF_2', type, '#skF_2': $i).
% 6.70/2.47  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.70/2.47  tff('#skF_3', type, '#skF_3': $i).
% 6.70/2.47  tff('#skF_1', type, '#skF_1': $i).
% 6.70/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.70/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.70/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.70/2.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.70/2.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.70/2.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.70/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.70/2.47  
% 6.99/2.48  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tops_2)).
% 6.99/2.48  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.99/2.48  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 6.99/2.48  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.99/2.48  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.99/2.48  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.99/2.48  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 6.99/2.48  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.99/2.48  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.99/2.48  tff(c_22, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.99/2.48  tff(c_95, plain, (![A_47, B_48, C_49]: (k7_subset_1(A_47, B_48, C_49)=k4_xboole_0(B_48, C_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.99/2.48  tff(c_230, plain, (![C_68]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_68)=k4_xboole_0('#skF_2', C_68))), inference(resolution, [status(thm)], [c_26, c_95])).
% 6.99/2.48  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k7_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.99/2.48  tff(c_239, plain, (![C_68]: (m1_subset_1(k4_xboole_0('#skF_2', C_68), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_230, c_10])).
% 6.99/2.48  tff(c_247, plain, (![C_68]: (m1_subset_1(k4_xboole_0('#skF_2', C_68), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_239])).
% 6.99/2.48  tff(c_6, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.99/2.48  tff(c_8, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.99/2.48  tff(c_29, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 6.99/2.48  tff(c_110, plain, (![A_7, C_49]: (k7_subset_1(A_7, A_7, C_49)=k4_xboole_0(A_7, C_49))), inference(resolution, [status(thm)], [c_29, c_95])).
% 6.99/2.48  tff(c_82, plain, (![A_40, B_41, C_42]: (m1_subset_1(k7_subset_1(A_40, B_41, C_42), k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.99/2.48  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.99/2.48  tff(c_86, plain, (![A_40, B_41, C_42]: (r1_tarski(k7_subset_1(A_40, B_41, C_42), A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(resolution, [status(thm)], [c_82, c_14])).
% 6.99/2.48  tff(c_175, plain, (![B_59, A_60, C_61]: (v1_tops_2(B_59, A_60) | ~v1_tops_2(C_61, A_60) | ~r1_tarski(B_59, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60)))) | ~m1_subset_1(B_59, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60)))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.99/2.48  tff(c_1942, plain, (![A_212, B_213, C_214, A_215]: (v1_tops_2(k7_subset_1(A_212, B_213, C_214), A_215) | ~v1_tops_2(A_212, A_215) | ~m1_subset_1(A_212, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215)))) | ~m1_subset_1(k7_subset_1(A_212, B_213, C_214), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215)))) | ~l1_pre_topc(A_215) | ~m1_subset_1(B_213, k1_zfmisc_1(A_212)))), inference(resolution, [status(thm)], [c_86, c_175])).
% 6.99/2.48  tff(c_1972, plain, (![A_7, C_49, A_215]: (v1_tops_2(k7_subset_1(A_7, A_7, C_49), A_215) | ~v1_tops_2(A_7, A_215) | ~m1_subset_1(A_7, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215)))) | ~m1_subset_1(k4_xboole_0(A_7, C_49), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_215)))) | ~l1_pre_topc(A_215) | ~m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_1942])).
% 6.99/2.48  tff(c_6511, plain, (![A_511, C_512, A_513]: (v1_tops_2(k4_xboole_0(A_511, C_512), A_513) | ~v1_tops_2(A_511, A_513) | ~m1_subset_1(A_511, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_513)))) | ~m1_subset_1(k4_xboole_0(A_511, C_512), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_513)))) | ~l1_pre_topc(A_513))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_110, c_1972])).
% 6.99/2.48  tff(c_6558, plain, (![C_68]: (v1_tops_2(k4_xboole_0('#skF_2', C_68), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_247, c_6511])).
% 6.99/2.48  tff(c_6608, plain, (![C_68]: (v1_tops_2(k4_xboole_0('#skF_2', C_68), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_6558])).
% 6.99/2.48  tff(c_109, plain, (![C_49]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_49)=k4_xboole_0('#skF_2', C_49))), inference(resolution, [status(thm)], [c_26, c_95])).
% 6.99/2.48  tff(c_20, plain, (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.99/2.48  tff(c_229, plain, (~v1_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_20])).
% 6.99/2.48  tff(c_6618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6608, c_229])).
% 6.99/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.99/2.48  
% 6.99/2.48  Inference rules
% 6.99/2.48  ----------------------
% 6.99/2.48  #Ref     : 0
% 6.99/2.48  #Sup     : 1477
% 6.99/2.48  #Fact    : 0
% 6.99/2.48  #Define  : 0
% 6.99/2.48  #Split   : 1
% 6.99/2.48  #Chain   : 0
% 6.99/2.48  #Close   : 0
% 6.99/2.48  
% 6.99/2.48  Ordering : KBO
% 6.99/2.48  
% 6.99/2.48  Simplification rules
% 6.99/2.48  ----------------------
% 6.99/2.48  #Subsume      : 240
% 6.99/2.48  #Demod        : 707
% 6.99/2.48  #Tautology    : 362
% 6.99/2.48  #SimpNegUnit  : 0
% 6.99/2.48  #BackRed      : 2
% 6.99/2.48  
% 6.99/2.48  #Partial instantiations: 0
% 6.99/2.48  #Strategies tried      : 1
% 6.99/2.48  
% 6.99/2.48  Timing (in seconds)
% 6.99/2.48  ----------------------
% 6.99/2.49  Preprocessing        : 0.30
% 6.99/2.49  Parsing              : 0.17
% 6.99/2.49  CNF conversion       : 0.02
% 6.99/2.49  Main loop            : 1.41
% 6.99/2.49  Inferencing          : 0.43
% 6.99/2.49  Reduction            : 0.48
% 6.99/2.49  Demodulation         : 0.38
% 6.99/2.49  BG Simplification    : 0.06
% 6.99/2.49  Subsumption          : 0.34
% 6.99/2.49  Abstraction          : 0.07
% 6.99/2.49  MUC search           : 0.00
% 6.99/2.49  Cooper               : 0.00
% 6.99/2.49  Total                : 1.73
% 6.99/2.49  Index Insertion      : 0.00
% 6.99/2.49  Index Deletion       : 0.00
% 6.99/2.49  Index Matching       : 0.00
% 6.99/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
