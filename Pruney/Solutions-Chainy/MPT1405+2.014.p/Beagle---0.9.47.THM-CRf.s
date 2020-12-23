%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:31 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 142 expanded)
%              Number of leaves         :   32 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 291 expanded)
%              Number of equality atoms :    9 (  31 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

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

tff(c_104,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | v1_xboole_0(B_42)
      | ~ m1_subset_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [A_46,A_47] :
      ( r1_tarski(A_46,A_47)
      | v1_xboole_0(k1_zfmisc_1(A_47))
      | ~ m1_subset_1(A_46,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_138,plain,
    ( r1_tarski('#skF_4',k2_struct_0('#skF_3'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_72,c_128])).

tff(c_146,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_138])).

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

tff(c_327,plain,(
    ! [C_76,A_77,B_78] :
      ( m2_connsp_2(C_76,A_77,B_78)
      | ~ r1_tarski(B_78,k1_tops_1(A_77,C_76))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_916,plain,(
    ! [A_122,B_123] :
      ( m2_connsp_2(k2_struct_0(A_122),A_122,B_123)
      | ~ r1_tarski(B_123,k2_struct_0(A_122))
      | ~ m1_subset_1(k2_struct_0(A_122),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_327])).

tff(c_924,plain,(
    ! [B_123] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_123)
      | ~ r1_tarski(B_123,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_916])).

tff(c_929,plain,(
    ! [B_124] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_124)
      | ~ r1_tarski(B_124,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_46,c_44,c_71,c_49,c_924])).

tff(c_956,plain,
    ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_929])).

tff(c_980,plain,(
    m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_956])).

tff(c_982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_980])).

tff(c_984,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_85,plain,(
    ! [A_9] :
      ( v1_xboole_0(A_9)
      | ~ v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_49,c_77])).

tff(c_988,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_984,c_85])).

tff(c_994,plain,(
    ! [A_127] :
      ( ~ v1_xboole_0(k2_struct_0(A_127))
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_997,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_988,c_994])).

tff(c_1000,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_997])).

tff(c_1003,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1000])).

tff(c_1007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:59:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.66  
% 3.39/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.67  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.39/1.67  
% 3.39/1.67  %Foreground sorts:
% 3.39/1.67  
% 3.39/1.67  
% 3.39/1.67  %Background operators:
% 3.39/1.67  
% 3.39/1.67  
% 3.39/1.67  %Foreground operators:
% 3.39/1.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.39/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.39/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.67  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.39/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.39/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.39/1.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.39/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.39/1.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.39/1.67  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.39/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.67  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.39/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.67  
% 3.39/1.68  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 3.39/1.68  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.39/1.68  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.39/1.68  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.39/1.68  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.39/1.68  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.39/1.68  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.39/1.68  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.39/1.68  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.39/1.68  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.39/1.68  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.39/1.68  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.39/1.68  tff(c_30, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.39/1.68  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.39/1.68  tff(c_40, plain, (~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.39/1.68  tff(c_61, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/1.68  tff(c_67, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_30, c_61])).
% 3.39/1.68  tff(c_71, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_67])).
% 3.39/1.68  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.39/1.68  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_42])).
% 3.39/1.68  tff(c_77, plain, (![B_31, A_32]: (v1_xboole_0(B_31) | ~m1_subset_1(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.39/1.68  tff(c_84, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_72, c_77])).
% 3.39/1.68  tff(c_92, plain, (~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_84])).
% 3.39/1.68  tff(c_104, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | v1_xboole_0(B_42) | ~m1_subset_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.68  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.68  tff(c_128, plain, (![A_46, A_47]: (r1_tarski(A_46, A_47) | v1_xboole_0(k1_zfmisc_1(A_47)) | ~m1_subset_1(A_46, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_104, c_2])).
% 3.39/1.68  tff(c_138, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_72, c_128])).
% 3.39/1.68  tff(c_146, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_92, c_138])).
% 3.39/1.68  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.39/1.68  tff(c_22, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.39/1.68  tff(c_24, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.39/1.68  tff(c_49, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 3.39/1.68  tff(c_34, plain, (![A_15]: (k1_tops_1(A_15, k2_struct_0(A_15))=k2_struct_0(A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.39/1.68  tff(c_327, plain, (![C_76, A_77, B_78]: (m2_connsp_2(C_76, A_77, B_78) | ~r1_tarski(B_78, k1_tops_1(A_77, C_76)) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.39/1.68  tff(c_916, plain, (![A_122, B_123]: (m2_connsp_2(k2_struct_0(A_122), A_122, B_123) | ~r1_tarski(B_123, k2_struct_0(A_122)) | ~m1_subset_1(k2_struct_0(A_122), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122))), inference(superposition, [status(thm), theory('equality')], [c_34, c_327])).
% 3.39/1.68  tff(c_924, plain, (![B_123]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_123) | ~r1_tarski(B_123, k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_916])).
% 3.39/1.68  tff(c_929, plain, (![B_124]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_124) | ~r1_tarski(B_124, k2_struct_0('#skF_3')) | ~m1_subset_1(B_124, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_46, c_44, c_71, c_49, c_924])).
% 3.39/1.68  tff(c_956, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_929])).
% 3.39/1.68  tff(c_980, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_956])).
% 3.39/1.68  tff(c_982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_980])).
% 3.39/1.68  tff(c_984, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_84])).
% 3.39/1.68  tff(c_85, plain, (![A_9]: (v1_xboole_0(A_9) | ~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_49, c_77])).
% 3.39/1.68  tff(c_988, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_984, c_85])).
% 3.39/1.68  tff(c_994, plain, (![A_127]: (~v1_xboole_0(k2_struct_0(A_127)) | ~l1_struct_0(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.39/1.68  tff(c_997, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_988, c_994])).
% 3.39/1.68  tff(c_1000, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_997])).
% 3.39/1.68  tff(c_1003, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1000])).
% 3.39/1.68  tff(c_1007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1003])).
% 3.39/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.68  
% 3.39/1.68  Inference rules
% 3.39/1.68  ----------------------
% 3.39/1.68  #Ref     : 0
% 3.39/1.68  #Sup     : 192
% 3.39/1.68  #Fact    : 0
% 3.39/1.68  #Define  : 0
% 3.39/1.68  #Split   : 4
% 3.39/1.68  #Chain   : 0
% 3.39/1.68  #Close   : 0
% 3.39/1.68  
% 3.39/1.68  Ordering : KBO
% 3.39/1.68  
% 3.39/1.68  Simplification rules
% 3.39/1.68  ----------------------
% 3.39/1.68  #Subsume      : 29
% 3.39/1.68  #Demod        : 94
% 3.39/1.68  #Tautology    : 47
% 3.39/1.68  #SimpNegUnit  : 34
% 3.39/1.68  #BackRed      : 1
% 3.39/1.68  
% 3.39/1.68  #Partial instantiations: 0
% 3.39/1.68  #Strategies tried      : 1
% 3.39/1.68  
% 3.39/1.68  Timing (in seconds)
% 3.39/1.68  ----------------------
% 3.39/1.68  Preprocessing        : 0.36
% 3.39/1.68  Parsing              : 0.18
% 3.39/1.68  CNF conversion       : 0.03
% 3.39/1.68  Main loop            : 0.44
% 3.39/1.68  Inferencing          : 0.15
% 3.39/1.68  Reduction            : 0.12
% 3.39/1.68  Demodulation         : 0.08
% 3.39/1.68  BG Simplification    : 0.03
% 3.39/1.68  Subsumption          : 0.11
% 3.39/1.68  Abstraction          : 0.03
% 3.39/1.68  MUC search           : 0.00
% 3.39/1.68  Cooper               : 0.00
% 3.39/1.68  Total                : 0.83
% 3.39/1.68  Index Insertion      : 0.00
% 3.39/1.68  Index Deletion       : 0.00
% 3.39/1.68  Index Matching       : 0.00
% 3.39/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
