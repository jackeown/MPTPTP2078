%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:31 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 151 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 311 expanded)
%              Number of equality atoms :    9 (  35 expanded)
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

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_55,axiom,(
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

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_91,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_61,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_71,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_67])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_42])).

tff(c_77,plain,(
    ! [B_31,A_32] :
      ( v1_xboole_0(B_31)
      | ~ m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_72,c_77])).

tff(c_92,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_118,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,B_40)
      | v1_xboole_0(B_40)
      | ~ m1_subset_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    ! [A_44,A_45] :
      ( r1_tarski(A_44,A_45)
      | v1_xboole_0(k1_zfmisc_1(A_45))
      | ~ m1_subset_1(A_44,k1_zfmisc_1(A_45)) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_149,plain,
    ( r1_tarski('#skF_4',k2_struct_0('#skF_3'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_72,c_142])).

tff(c_156,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_149])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_22,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_34,plain,(
    ! [A_15] :
      ( k1_tops_1(A_15,k2_struct_0(A_15)) = k2_struct_0(A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_226,plain,(
    ! [C_64,A_65,B_66] :
      ( m2_connsp_2(C_64,A_65,B_66)
      | ~ r1_tarski(B_66,k1_tops_1(A_65,C_64))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_835,plain,(
    ! [A_116,B_117] :
      ( m2_connsp_2(k2_struct_0(A_116),A_116,B_117)
      | ~ r1_tarski(B_117,k2_struct_0(A_116))
      | ~ m1_subset_1(k2_struct_0(A_116),k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_226])).

tff(c_843,plain,(
    ! [B_117] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_117)
      | ~ r1_tarski(B_117,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_835])).

tff(c_848,plain,(
    ! [B_118] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_118)
      | ~ r1_tarski(B_118,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_46,c_44,c_71,c_49,c_843])).

tff(c_871,plain,
    ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_848])).

tff(c_891,plain,(
    m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_871])).

tff(c_893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_891])).

tff(c_895,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_85,plain,(
    ! [A_9] :
      ( v1_xboole_0(A_9)
      | ~ v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_49,c_77])).

tff(c_899,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_895,c_85])).

tff(c_905,plain,(
    ! [A_121] :
      ( ~ v1_xboole_0(u1_struct_0(A_121))
      | ~ l1_struct_0(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_908,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_905])).

tff(c_910,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_908])).

tff(c_911,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_910])).

tff(c_914,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_911])).

tff(c_918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.61  
% 3.29/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.61  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.29/1.61  
% 3.29/1.61  %Foreground sorts:
% 3.29/1.61  
% 3.29/1.61  
% 3.29/1.61  %Background operators:
% 3.29/1.61  
% 3.29/1.61  
% 3.29/1.61  %Foreground operators:
% 3.29/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.29/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.29/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.29/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.29/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.29/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.29/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.29/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.29/1.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.29/1.61  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.29/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.29/1.61  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.29/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.61  
% 3.71/1.62  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 3.71/1.62  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.71/1.62  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.71/1.62  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.71/1.62  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.71/1.62  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.71/1.62  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.71/1.62  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.71/1.62  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 3.71/1.62  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.71/1.62  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.71/1.62  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.71/1.62  tff(c_30, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.71/1.62  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.71/1.62  tff(c_40, plain, (~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.71/1.62  tff(c_61, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.71/1.62  tff(c_67, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_30, c_61])).
% 3.71/1.62  tff(c_71, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_67])).
% 3.71/1.62  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.71/1.62  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_42])).
% 3.71/1.62  tff(c_77, plain, (![B_31, A_32]: (v1_xboole_0(B_31) | ~m1_subset_1(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.71/1.62  tff(c_84, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_72, c_77])).
% 3.71/1.62  tff(c_92, plain, (~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_84])).
% 3.71/1.62  tff(c_118, plain, (![A_39, B_40]: (r2_hidden(A_39, B_40) | v1_xboole_0(B_40) | ~m1_subset_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.71/1.62  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.71/1.62  tff(c_142, plain, (![A_44, A_45]: (r1_tarski(A_44, A_45) | v1_xboole_0(k1_zfmisc_1(A_45)) | ~m1_subset_1(A_44, k1_zfmisc_1(A_45)))), inference(resolution, [status(thm)], [c_118, c_2])).
% 3.71/1.62  tff(c_149, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_72, c_142])).
% 3.71/1.62  tff(c_156, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_92, c_149])).
% 3.71/1.62  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.71/1.62  tff(c_22, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.71/1.62  tff(c_24, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.71/1.62  tff(c_49, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 3.71/1.62  tff(c_34, plain, (![A_15]: (k1_tops_1(A_15, k2_struct_0(A_15))=k2_struct_0(A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.71/1.62  tff(c_226, plain, (![C_64, A_65, B_66]: (m2_connsp_2(C_64, A_65, B_66) | ~r1_tarski(B_66, k1_tops_1(A_65, C_64)) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.71/1.62  tff(c_835, plain, (![A_116, B_117]: (m2_connsp_2(k2_struct_0(A_116), A_116, B_117) | ~r1_tarski(B_117, k2_struct_0(A_116)) | ~m1_subset_1(k2_struct_0(A_116), k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116))), inference(superposition, [status(thm), theory('equality')], [c_34, c_226])).
% 3.71/1.62  tff(c_843, plain, (![B_117]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_117) | ~r1_tarski(B_117, k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_835])).
% 3.71/1.62  tff(c_848, plain, (![B_118]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_118) | ~r1_tarski(B_118, k2_struct_0('#skF_3')) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_46, c_44, c_71, c_49, c_843])).
% 3.71/1.62  tff(c_871, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_848])).
% 3.71/1.62  tff(c_891, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_871])).
% 3.71/1.62  tff(c_893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_891])).
% 3.71/1.62  tff(c_895, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_84])).
% 3.71/1.62  tff(c_85, plain, (![A_9]: (v1_xboole_0(A_9) | ~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_49, c_77])).
% 3.71/1.62  tff(c_899, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_895, c_85])).
% 3.71/1.62  tff(c_905, plain, (![A_121]: (~v1_xboole_0(u1_struct_0(A_121)) | ~l1_struct_0(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.71/1.62  tff(c_908, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_71, c_905])).
% 3.71/1.62  tff(c_910, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_899, c_908])).
% 3.71/1.62  tff(c_911, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_910])).
% 3.71/1.62  tff(c_914, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_911])).
% 3.71/1.62  tff(c_918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_914])).
% 3.71/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.62  
% 3.71/1.62  Inference rules
% 3.71/1.62  ----------------------
% 3.71/1.62  #Ref     : 0
% 3.71/1.62  #Sup     : 174
% 3.71/1.62  #Fact    : 0
% 3.71/1.62  #Define  : 0
% 3.71/1.62  #Split   : 5
% 3.71/1.62  #Chain   : 0
% 3.71/1.62  #Close   : 0
% 3.71/1.62  
% 3.71/1.62  Ordering : KBO
% 3.71/1.62  
% 3.71/1.62  Simplification rules
% 3.71/1.62  ----------------------
% 3.71/1.62  #Subsume      : 27
% 3.71/1.62  #Demod        : 77
% 3.71/1.62  #Tautology    : 38
% 3.71/1.62  #SimpNegUnit  : 31
% 3.71/1.62  #BackRed      : 1
% 3.71/1.62  
% 3.71/1.62  #Partial instantiations: 0
% 3.71/1.63  #Strategies tried      : 1
% 3.71/1.63  
% 3.71/1.63  Timing (in seconds)
% 3.71/1.63  ----------------------
% 3.71/1.63  Preprocessing        : 0.33
% 3.71/1.63  Parsing              : 0.17
% 3.71/1.63  CNF conversion       : 0.02
% 3.71/1.63  Main loop            : 0.49
% 3.71/1.63  Inferencing          : 0.18
% 3.71/1.63  Reduction            : 0.13
% 3.71/1.63  Demodulation         : 0.09
% 3.71/1.63  BG Simplification    : 0.03
% 3.71/1.63  Subsumption          : 0.12
% 3.71/1.63  Abstraction          : 0.03
% 3.71/1.63  MUC search           : 0.00
% 3.71/1.63  Cooper               : 0.00
% 3.71/1.63  Total                : 0.85
% 3.71/1.63  Index Insertion      : 0.00
% 3.71/1.63  Index Deletion       : 0.00
% 3.71/1.63  Index Matching       : 0.00
% 3.71/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
