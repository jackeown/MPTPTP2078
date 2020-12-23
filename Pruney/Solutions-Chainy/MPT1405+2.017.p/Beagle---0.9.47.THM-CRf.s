%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:32 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   57 (  93 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 177 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_39,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_73,axiom,(
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

tff(c_32,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_24,c_54])).

tff(c_63,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_59])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_34])).

tff(c_18,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_32,A_1] :
      ( r1_tarski(A_32,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_32,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_83,plain,(
    ! [A_34,A_35] :
      ( r1_tarski(A_34,A_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(A_35)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_79])).

tff(c_90,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_83])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_41,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_26,plain,(
    ! [A_13] :
      ( k1_tops_1(A_13,k2_struct_0(A_13)) = k2_struct_0(A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    ! [C_48,A_49,B_50] :
      ( m2_connsp_2(C_48,A_49,B_50)
      | ~ r1_tarski(B_50,k1_tops_1(A_49,C_48))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_293,plain,(
    ! [A_73,B_74] :
      ( m2_connsp_2(k2_struct_0(A_73),A_73,B_74)
      | ~ r1_tarski(B_74,k2_struct_0(A_73))
      | ~ m1_subset_1(k2_struct_0(A_73),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_125])).

tff(c_295,plain,(
    ! [B_74] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_74)
      | ~ r1_tarski(B_74,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_293])).

tff(c_298,plain,(
    ! [B_75] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_75)
      | ~ r1_tarski(B_75,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_38,c_36,c_63,c_41,c_295])).

tff(c_301,plain,
    ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_64,c_298])).

tff(c_308,plain,(
    m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_301])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:29:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.38  
% 2.32/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.38  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.32/1.38  
% 2.32/1.38  %Foreground sorts:
% 2.32/1.38  
% 2.32/1.38  
% 2.32/1.38  %Background operators:
% 2.32/1.38  
% 2.32/1.38  
% 2.32/1.38  %Foreground operators:
% 2.32/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.32/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.38  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.32/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.32/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.32/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.32/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.32/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.32/1.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.32/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.38  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.32/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.38  
% 2.57/1.39  tff(f_86, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.57/1.39  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.57/1.39  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.57/1.39  tff(f_39, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.57/1.39  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.57/1.39  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.57/1.39  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.57/1.39  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.57/1.39  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.57/1.39  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.57/1.39  tff(c_32, plain, (~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.39  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.39  tff(c_24, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.39  tff(c_54, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.39  tff(c_59, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_24, c_54])).
% 2.57/1.39  tff(c_63, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_59])).
% 2.57/1.39  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.39  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_34])).
% 2.57/1.39  tff(c_18, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.39  tff(c_75, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | v1_xboole_0(B_33) | ~m1_subset_1(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.39  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.57/1.39  tff(c_79, plain, (![A_32, A_1]: (r1_tarski(A_32, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_32, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_75, c_2])).
% 2.57/1.39  tff(c_83, plain, (![A_34, A_35]: (r1_tarski(A_34, A_35) | ~m1_subset_1(A_34, k1_zfmisc_1(A_35)))), inference(negUnitSimplification, [status(thm)], [c_18, c_79])).
% 2.57/1.39  tff(c_90, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_83])).
% 2.57/1.39  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.39  tff(c_14, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.57/1.39  tff(c_16, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.57/1.39  tff(c_41, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 2.57/1.39  tff(c_26, plain, (![A_13]: (k1_tops_1(A_13, k2_struct_0(A_13))=k2_struct_0(A_13) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.57/1.39  tff(c_125, plain, (![C_48, A_49, B_50]: (m2_connsp_2(C_48, A_49, B_50) | ~r1_tarski(B_50, k1_tops_1(A_49, C_48)) | ~m1_subset_1(C_48, k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.57/1.39  tff(c_293, plain, (![A_73, B_74]: (m2_connsp_2(k2_struct_0(A_73), A_73, B_74) | ~r1_tarski(B_74, k2_struct_0(A_73)) | ~m1_subset_1(k2_struct_0(A_73), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(superposition, [status(thm), theory('equality')], [c_26, c_125])).
% 2.57/1.39  tff(c_295, plain, (![B_74]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_74) | ~r1_tarski(B_74, k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_293])).
% 2.57/1.39  tff(c_298, plain, (![B_75]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_75) | ~r1_tarski(B_75, k2_struct_0('#skF_3')) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_38, c_36, c_63, c_41, c_295])).
% 2.57/1.39  tff(c_301, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_64, c_298])).
% 2.57/1.39  tff(c_308, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_301])).
% 2.57/1.39  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_308])).
% 2.57/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.39  
% 2.57/1.39  Inference rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Ref     : 0
% 2.57/1.39  #Sup     : 53
% 2.57/1.39  #Fact    : 0
% 2.57/1.39  #Define  : 0
% 2.57/1.39  #Split   : 2
% 2.57/1.39  #Chain   : 0
% 2.57/1.39  #Close   : 0
% 2.57/1.39  
% 2.57/1.39  Ordering : KBO
% 2.57/1.39  
% 2.57/1.39  Simplification rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Subsume      : 3
% 2.57/1.39  #Demod        : 33
% 2.57/1.39  #Tautology    : 14
% 2.57/1.39  #SimpNegUnit  : 5
% 2.57/1.39  #BackRed      : 1
% 2.57/1.39  
% 2.57/1.39  #Partial instantiations: 0
% 2.57/1.39  #Strategies tried      : 1
% 2.57/1.39  
% 2.57/1.39  Timing (in seconds)
% 2.57/1.39  ----------------------
% 2.57/1.40  Preprocessing        : 0.34
% 2.57/1.40  Parsing              : 0.17
% 2.57/1.40  CNF conversion       : 0.03
% 2.57/1.40  Main loop            : 0.25
% 2.57/1.40  Inferencing          : 0.10
% 2.57/1.40  Reduction            : 0.07
% 2.57/1.40  Demodulation         : 0.05
% 2.57/1.40  BG Simplification    : 0.02
% 2.57/1.40  Subsumption          : 0.05
% 2.57/1.40  Abstraction          : 0.02
% 2.57/1.40  MUC search           : 0.00
% 2.57/1.40  Cooper               : 0.00
% 2.57/1.40  Total                : 0.62
% 2.57/1.40  Index Insertion      : 0.00
% 2.57/1.40  Index Deletion       : 0.00
% 2.57/1.40  Index Matching       : 0.00
% 2.57/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
