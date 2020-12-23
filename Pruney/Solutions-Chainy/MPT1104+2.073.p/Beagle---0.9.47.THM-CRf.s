%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:51 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 5.93s
% Verified   : 
% Statistics : Number of formulae       :   60 (  79 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 128 expanded)
%              Number of equality atoms :   31 (  56 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > m1_subset_1 > l1_struct_0 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k9_setfam_1 > k2_struct_0 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( k2_struct_0(A) = k4_subset_1(u1_struct_0(A),B,C)
                    & r1_xboole_0(B,C) )
                 => C = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_42,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2225,plain,(
    ! [A_123,B_124,C_125] :
      ( k4_subset_1(A_123,B_124,C_125) = k2_xboole_0(B_124,C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(A_123))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2373,plain,(
    ! [B_128] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_128,'#skF_3') = k2_xboole_0(B_128,'#skF_3')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_44,c_2225])).

tff(c_2383,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_2373])).

tff(c_2392,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2,c_2383])).

tff(c_40,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(k2_xboole_0(A_8,B_9),B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = A_19
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_146,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = A_46
      | ~ r1_xboole_0(A_46,B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_165,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_146])).

tff(c_24,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_79,plain,(
    ! [B_40,A_41] :
      ( r1_xboole_0(B_40,A_41)
      | ~ r1_xboole_0(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [B_15,A_14] : r1_xboole_0(B_15,k4_xboole_0(A_14,B_15)) ),
    inference(resolution,[status(thm)],[c_24,c_79])).

tff(c_162,plain,(
    ! [B_15,A_14] : k4_xboole_0(B_15,k4_xboole_0(A_14,B_15)) = B_15 ),
    inference(resolution,[status(thm)],[c_86,c_146])).

tff(c_694,plain,(
    ! [A_78,B_79] : k2_xboole_0(A_78,k4_xboole_0(B_79,A_78)) = k2_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_703,plain,(
    ! [A_78,B_79] : k4_xboole_0(k2_xboole_0(A_78,B_79),k4_xboole_0(B_79,A_78)) = k4_xboole_0(A_78,k4_xboole_0(B_79,A_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_12])).

tff(c_1611,plain,(
    ! [A_109,B_110] : k4_xboole_0(k2_xboole_0(A_109,B_110),k4_xboole_0(B_110,A_109)) = A_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_703])).

tff(c_1685,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),'#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_1611])).

tff(c_2396,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_1685])).

tff(c_1761,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1(k4_subset_1(A_111,B_112,C_113),k1_zfmisc_1(A_111))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_27,B_28,C_29] :
      ( k7_subset_1(A_27,B_28,C_29) = k4_xboole_0(B_28,C_29)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4994,plain,(
    ! [A_184,B_185,C_186,C_187] :
      ( k7_subset_1(A_184,k4_subset_1(A_184,B_185,C_186),C_187) = k4_xboole_0(k4_subset_1(A_184,B_185,C_186),C_187)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(A_184))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(A_184)) ) ),
    inference(resolution,[status(thm)],[c_1761,c_34])).

tff(c_5598,plain,(
    ! [B_206,C_207] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k4_subset_1(u1_struct_0('#skF_1'),B_206,'#skF_3'),C_207) = k4_xboole_0(k4_subset_1(u1_struct_0('#skF_1'),B_206,'#skF_3'),C_207)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_44,c_4994])).

tff(c_5610,plain,(
    ! [C_207] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_207) = k4_xboole_0(k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),C_207)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5598])).

tff(c_5616,plain,(
    ! [C_207] : k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_207) = k4_xboole_0(k2_struct_0('#skF_1'),C_207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_5610])).

tff(c_38,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),'#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_7153,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5616,c_38])).

tff(c_7156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2396,c_7153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:33:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.93/2.19  
% 5.93/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.93/2.19  %$ r1_xboole_0 > m1_subset_1 > l1_struct_0 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k9_setfam_1 > k2_struct_0 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.93/2.19  
% 5.93/2.19  %Foreground sorts:
% 5.93/2.19  
% 5.93/2.19  
% 5.93/2.19  %Background operators:
% 5.93/2.19  
% 5.93/2.19  
% 5.93/2.19  %Foreground operators:
% 5.93/2.19  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 5.93/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.93/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.93/2.19  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 5.93/2.19  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.93/2.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.93/2.19  tff('#skF_2', type, '#skF_2': $i).
% 5.93/2.19  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.93/2.19  tff('#skF_3', type, '#skF_3': $i).
% 5.93/2.19  tff('#skF_1', type, '#skF_1': $i).
% 5.93/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.93/2.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.93/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.93/2.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.93/2.19  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.93/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.93/2.19  
% 5.93/2.20  tff(f_109, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((k2_struct_0(A) = k4_subset_1(u1_struct_0(A), B, C)) & r1_xboole_0(B, C)) => (C = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_pre_topc)).
% 5.93/2.20  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.93/2.20  tff(f_88, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.93/2.20  tff(f_38, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.93/2.20  tff(f_76, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 5.93/2.20  tff(f_68, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.93/2.20  tff(f_32, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.93/2.20  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.93/2.20  tff(f_82, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.93/2.20  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.93/2.20  tff(c_42, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.93/2.20  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.93/2.20  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.93/2.20  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.93/2.20  tff(c_2225, plain, (![A_123, B_124, C_125]: (k4_subset_1(A_123, B_124, C_125)=k2_xboole_0(B_124, C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(A_123)) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.93/2.20  tff(c_2373, plain, (![B_128]: (k4_subset_1(u1_struct_0('#skF_1'), B_128, '#skF_3')=k2_xboole_0(B_128, '#skF_3') | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_44, c_2225])).
% 5.93/2.20  tff(c_2383, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_2373])).
% 5.93/2.20  tff(c_2392, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2, c_2383])).
% 5.93/2.20  tff(c_40, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.93/2.20  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(k2_xboole_0(A_8, B_9), B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.93/2.20  tff(c_28, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=A_19 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.93/2.20  tff(c_146, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=A_46 | ~r1_xboole_0(A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 5.93/2.20  tff(c_165, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_40, c_146])).
% 5.93/2.20  tff(c_24, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.93/2.20  tff(c_79, plain, (![B_40, A_41]: (r1_xboole_0(B_40, A_41) | ~r1_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.93/2.20  tff(c_86, plain, (![B_15, A_14]: (r1_xboole_0(B_15, k4_xboole_0(A_14, B_15)))), inference(resolution, [status(thm)], [c_24, c_79])).
% 5.93/2.20  tff(c_162, plain, (![B_15, A_14]: (k4_xboole_0(B_15, k4_xboole_0(A_14, B_15))=B_15)), inference(resolution, [status(thm)], [c_86, c_146])).
% 5.93/2.20  tff(c_694, plain, (![A_78, B_79]: (k2_xboole_0(A_78, k4_xboole_0(B_79, A_78))=k2_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.93/2.20  tff(c_703, plain, (![A_78, B_79]: (k4_xboole_0(k2_xboole_0(A_78, B_79), k4_xboole_0(B_79, A_78))=k4_xboole_0(A_78, k4_xboole_0(B_79, A_78)))), inference(superposition, [status(thm), theory('equality')], [c_694, c_12])).
% 5.93/2.20  tff(c_1611, plain, (![A_109, B_110]: (k4_xboole_0(k2_xboole_0(A_109, B_110), k4_xboole_0(B_110, A_109))=A_109)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_703])).
% 5.93/2.20  tff(c_1685, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_165, c_1611])).
% 5.93/2.20  tff(c_2396, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_1685])).
% 5.93/2.20  tff(c_1761, plain, (![A_111, B_112, C_113]: (m1_subset_1(k4_subset_1(A_111, B_112, C_113), k1_zfmisc_1(A_111)) | ~m1_subset_1(C_113, k1_zfmisc_1(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.93/2.20  tff(c_34, plain, (![A_27, B_28, C_29]: (k7_subset_1(A_27, B_28, C_29)=k4_xboole_0(B_28, C_29) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.93/2.20  tff(c_4994, plain, (![A_184, B_185, C_186, C_187]: (k7_subset_1(A_184, k4_subset_1(A_184, B_185, C_186), C_187)=k4_xboole_0(k4_subset_1(A_184, B_185, C_186), C_187) | ~m1_subset_1(C_186, k1_zfmisc_1(A_184)) | ~m1_subset_1(B_185, k1_zfmisc_1(A_184)))), inference(resolution, [status(thm)], [c_1761, c_34])).
% 5.93/2.20  tff(c_5598, plain, (![B_206, C_207]: (k7_subset_1(u1_struct_0('#skF_1'), k4_subset_1(u1_struct_0('#skF_1'), B_206, '#skF_3'), C_207)=k4_xboole_0(k4_subset_1(u1_struct_0('#skF_1'), B_206, '#skF_3'), C_207) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_44, c_4994])).
% 5.93/2.20  tff(c_5610, plain, (![C_207]: (k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_207)=k4_xboole_0(k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), C_207) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_42, c_5598])).
% 5.93/2.20  tff(c_5616, plain, (![C_207]: (k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), C_207)=k4_xboole_0(k2_struct_0('#skF_1'), C_207))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_5610])).
% 5.93/2.20  tff(c_38, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), '#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.93/2.20  tff(c_7153, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5616, c_38])).
% 5.93/2.20  tff(c_7156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2396, c_7153])).
% 5.93/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.93/2.20  
% 5.93/2.20  Inference rules
% 5.93/2.20  ----------------------
% 5.93/2.20  #Ref     : 0
% 5.93/2.20  #Sup     : 1750
% 5.93/2.20  #Fact    : 0
% 5.93/2.20  #Define  : 0
% 5.93/2.20  #Split   : 2
% 5.93/2.20  #Chain   : 0
% 5.93/2.20  #Close   : 0
% 5.93/2.20  
% 5.93/2.20  Ordering : KBO
% 5.93/2.20  
% 5.93/2.20  Simplification rules
% 5.93/2.20  ----------------------
% 5.93/2.20  #Subsume      : 147
% 5.93/2.20  #Demod        : 1621
% 5.93/2.20  #Tautology    : 1151
% 5.93/2.20  #SimpNegUnit  : 7
% 5.93/2.20  #BackRed      : 5
% 5.93/2.20  
% 5.93/2.20  #Partial instantiations: 0
% 5.93/2.20  #Strategies tried      : 1
% 5.93/2.20  
% 5.93/2.20  Timing (in seconds)
% 5.93/2.20  ----------------------
% 5.93/2.21  Preprocessing        : 0.32
% 5.93/2.21  Parsing              : 0.18
% 5.93/2.21  CNF conversion       : 0.02
% 5.93/2.21  Main loop            : 1.12
% 5.93/2.21  Inferencing          : 0.33
% 5.93/2.21  Reduction            : 0.52
% 5.93/2.21  Demodulation         : 0.43
% 5.93/2.21  BG Simplification    : 0.03
% 5.93/2.21  Subsumption          : 0.18
% 5.93/2.21  Abstraction          : 0.05
% 5.93/2.21  MUC search           : 0.00
% 5.93/2.21  Cooper               : 0.00
% 5.93/2.21  Total                : 1.47
% 5.93/2.21  Index Insertion      : 0.00
% 5.93/2.21  Index Deletion       : 0.00
% 5.93/2.21  Index Matching       : 0.00
% 5.93/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
