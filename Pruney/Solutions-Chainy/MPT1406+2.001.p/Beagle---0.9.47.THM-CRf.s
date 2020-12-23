%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:34 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   47 (  73 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 177 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_connsp_2(C,A,B)
               => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_connsp_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_16,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    m2_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_110,plain,(
    ! [C_35,A_36,B_37] :
      ( m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m2_connsp_2(C_35,A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_112,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_110])).

tff(c_115,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_112])).

tff(c_311,plain,(
    ! [B_54,A_55,C_56] :
      ( r1_tarski(B_54,k1_tops_1(A_55,C_56))
      | ~ m2_connsp_2(C_56,A_55,B_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_313,plain,(
    ! [B_54] :
      ( r1_tarski(B_54,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_115,c_311])).

tff(c_527,plain,(
    ! [B_68] :
      ( r1_tarski(B_68,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_313])).

tff(c_533,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ m2_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_527])).

tff(c_537,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_533])).

tff(c_8,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k1_tops_1(A_8,B_10),B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_117,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_115,c_8])).

tff(c_120,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_124,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_120,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,k2_xboole_0(C_31,B_32))
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [A_38,B_39,A_40] :
      ( r1_tarski(A_38,k2_xboole_0(B_39,A_40))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_164,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_3')
      | ~ r1_tarski(A_38,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_155])).

tff(c_546,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_537,c_164])).

tff(c_557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.32  
% 2.56/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.33  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.56/1.33  
% 2.56/1.33  %Foreground sorts:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Background operators:
% 2.56/1.33  
% 2.56/1.33  
% 2.56/1.33  %Foreground operators:
% 2.56/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.33  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.56/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.56/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.56/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.33  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.56/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.33  
% 2.56/1.34  tff(f_83, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m2_connsp_2(C, A, B) => r1_tarski(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_connsp_2)).
% 2.56/1.34  tff(f_67, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m2_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 2.56/1.34  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.56/1.34  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.56/1.34  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.56/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.56/1.34  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.56/1.34  tff(c_16, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.34  tff(c_18, plain, (m2_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.34  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.34  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.34  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.34  tff(c_110, plain, (![C_35, A_36, B_37]: (m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~m2_connsp_2(C_35, A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.56/1.34  tff(c_112, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_110])).
% 2.56/1.34  tff(c_115, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_112])).
% 2.56/1.34  tff(c_311, plain, (![B_54, A_55, C_56]: (r1_tarski(B_54, k1_tops_1(A_55, C_56)) | ~m2_connsp_2(C_56, A_55, B_54) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.34  tff(c_313, plain, (![B_54]: (r1_tarski(B_54, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_115, c_311])).
% 2.56/1.34  tff(c_527, plain, (![B_68]: (r1_tarski(B_68, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_313])).
% 2.56/1.34  tff(c_533, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_527])).
% 2.56/1.34  tff(c_537, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_533])).
% 2.56/1.34  tff(c_8, plain, (![A_8, B_10]: (r1_tarski(k1_tops_1(A_8, B_10), B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.34  tff(c_117, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_115, c_8])).
% 2.56/1.34  tff(c_120, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_117])).
% 2.56/1.34  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.34  tff(c_124, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_120, c_6])).
% 2.56/1.34  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.34  tff(c_61, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, k2_xboole_0(C_31, B_32)) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.34  tff(c_155, plain, (![A_38, B_39, A_40]: (r1_tarski(A_38, k2_xboole_0(B_39, A_40)) | ~r1_tarski(A_38, B_39))), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 2.56/1.34  tff(c_164, plain, (![A_38]: (r1_tarski(A_38, '#skF_3') | ~r1_tarski(A_38, k1_tops_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_124, c_155])).
% 2.56/1.34  tff(c_546, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_537, c_164])).
% 2.56/1.34  tff(c_557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_546])).
% 2.56/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  Inference rules
% 2.56/1.34  ----------------------
% 2.56/1.34  #Ref     : 0
% 2.56/1.34  #Sup     : 144
% 2.56/1.34  #Fact    : 0
% 2.56/1.34  #Define  : 0
% 2.56/1.34  #Split   : 2
% 2.56/1.34  #Chain   : 0
% 2.56/1.34  #Close   : 0
% 2.56/1.34  
% 2.56/1.34  Ordering : KBO
% 2.56/1.34  
% 2.56/1.34  Simplification rules
% 2.56/1.34  ----------------------
% 2.56/1.34  #Subsume      : 27
% 2.56/1.34  #Demod        : 42
% 2.56/1.34  #Tautology    : 41
% 2.56/1.34  #SimpNegUnit  : 1
% 2.56/1.34  #BackRed      : 0
% 2.56/1.34  
% 2.56/1.34  #Partial instantiations: 0
% 2.56/1.34  #Strategies tried      : 1
% 2.56/1.34  
% 2.56/1.34  Timing (in seconds)
% 2.56/1.34  ----------------------
% 2.56/1.34  Preprocessing        : 0.28
% 2.56/1.34  Parsing              : 0.16
% 2.56/1.34  CNF conversion       : 0.02
% 2.56/1.34  Main loop            : 0.30
% 2.56/1.34  Inferencing          : 0.11
% 2.56/1.34  Reduction            : 0.10
% 2.56/1.34  Demodulation         : 0.08
% 2.56/1.34  BG Simplification    : 0.02
% 2.56/1.34  Subsumption          : 0.06
% 2.56/1.34  Abstraction          : 0.01
% 2.56/1.34  MUC search           : 0.00
% 2.56/1.34  Cooper               : 0.00
% 2.56/1.34  Total                : 0.61
% 2.56/1.34  Index Insertion      : 0.00
% 2.56/1.34  Index Deletion       : 0.00
% 2.56/1.34  Index Matching       : 0.00
% 2.56/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
