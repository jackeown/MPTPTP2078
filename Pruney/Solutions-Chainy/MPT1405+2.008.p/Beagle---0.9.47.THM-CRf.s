%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:31 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 142 expanded)
%              Number of leaves         :   38 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 266 expanded)
%              Number of equality atoms :    9 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_82,axiom,(
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

tff(c_40,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_15] : m1_subset_1(k2_subset_1(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    ! [A_15] : m1_subset_1(A_15,k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_117,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | v1_xboole_0(B_52)
      | ~ m1_subset_1(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_137,plain,(
    ! [A_55,A_56] :
      ( r1_tarski(A_55,A_56)
      | v1_xboole_0(k1_zfmisc_1(A_56))
      | ~ m1_subset_1(A_55,k1_zfmisc_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_117,c_10])).

tff(c_146,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,A_57)
      | v1_xboole_0(k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_49,c_137])).

tff(c_89,plain,(
    ! [C_43,A_44] :
      ( r2_hidden(C_43,k1_zfmisc_1(A_44))
      | ~ r1_tarski(C_43,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_44,C_43] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_44))
      | ~ r1_tarski(C_43,A_44) ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_159,plain,(
    ! [C_60,A_61] :
      ( ~ r1_tarski(C_60,A_61)
      | r1_tarski(A_61,A_61) ) ),
    inference(resolution,[status(thm)],[c_146,c_97])).

tff(c_168,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(resolution,[status(thm)],[c_8,c_159])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_63,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_73,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_77,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_42])).

tff(c_144,plain,
    ( r1_tarski('#skF_5',k2_struct_0('#skF_4'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_78,c_137])).

tff(c_172,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_176,plain,(
    ! [C_63] : ~ r1_tarski(C_63,k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_172,c_97])).

tff(c_188,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_168,c_176])).

tff(c_189,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    ! [A_22] :
      ( k1_tops_1(A_22,k2_struct_0(A_22)) = k2_struct_0(A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_285,plain,(
    ! [C_88,A_89,B_90] :
      ( m2_connsp_2(C_88,A_89,B_90)
      | ~ r1_tarski(B_90,k1_tops_1(A_89,C_88))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_421,plain,(
    ! [A_107,B_108] :
      ( m2_connsp_2(k2_struct_0(A_107),A_107,B_108)
      | ~ r1_tarski(B_108,k2_struct_0(A_107))
      | ~ m1_subset_1(k2_struct_0(A_107),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_285])).

tff(c_423,plain,(
    ! [B_108] :
      ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4',B_108)
      | ~ r1_tarski(B_108,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_421])).

tff(c_426,plain,(
    ! [B_109] :
      ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4',B_109)
      | ~ r1_tarski(B_109,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_46,c_44,c_77,c_49,c_423])).

tff(c_429,plain,
    ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5')
    | ~ r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_78,c_426])).

tff(c_436,plain,(
    m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_429])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.38  
% 2.68/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.39  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.68/1.39  
% 2.68/1.39  %Foreground sorts:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Background operators:
% 2.68/1.39  
% 2.68/1.39  
% 2.68/1.39  %Foreground operators:
% 2.68/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.68/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.68/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.68/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.68/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.68/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.68/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.68/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.68/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.68/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.39  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.68/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.68/1.39  
% 2.68/1.40  tff(f_95, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.68/1.40  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.68/1.40  tff(f_44, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.68/1.40  tff(f_46, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.68/1.40  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.68/1.40  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.68/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.68/1.40  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.68/1.40  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.68/1.40  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.68/1.40  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.68/1.40  tff(c_40, plain, (~m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.68/1.40  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.40  tff(c_22, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.68/1.40  tff(c_24, plain, (![A_15]: (m1_subset_1(k2_subset_1(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.40  tff(c_49, plain, (![A_15]: (m1_subset_1(A_15, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 2.68/1.40  tff(c_117, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | v1_xboole_0(B_52) | ~m1_subset_1(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.68/1.40  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.40  tff(c_137, plain, (![A_55, A_56]: (r1_tarski(A_55, A_56) | v1_xboole_0(k1_zfmisc_1(A_56)) | ~m1_subset_1(A_55, k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_117, c_10])).
% 2.68/1.40  tff(c_146, plain, (![A_57]: (r1_tarski(A_57, A_57) | v1_xboole_0(k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_49, c_137])).
% 2.68/1.40  tff(c_89, plain, (![C_43, A_44]: (r2_hidden(C_43, k1_zfmisc_1(A_44)) | ~r1_tarski(C_43, A_44))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.40  tff(c_97, plain, (![A_44, C_43]: (~v1_xboole_0(k1_zfmisc_1(A_44)) | ~r1_tarski(C_43, A_44))), inference(resolution, [status(thm)], [c_89, c_2])).
% 2.68/1.40  tff(c_159, plain, (![C_60, A_61]: (~r1_tarski(C_60, A_61) | r1_tarski(A_61, A_61))), inference(resolution, [status(thm)], [c_146, c_97])).
% 2.68/1.40  tff(c_168, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(resolution, [status(thm)], [c_8, c_159])).
% 2.68/1.40  tff(c_44, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.68/1.40  tff(c_32, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.68/1.40  tff(c_63, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.68/1.40  tff(c_73, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_32, c_63])).
% 2.68/1.40  tff(c_77, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_73])).
% 2.68/1.40  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.68/1.40  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_42])).
% 2.68/1.40  tff(c_144, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_78, c_137])).
% 2.68/1.40  tff(c_172, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_144])).
% 2.68/1.40  tff(c_176, plain, (![C_63]: (~r1_tarski(C_63, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_172, c_97])).
% 2.68/1.40  tff(c_188, plain, $false, inference(resolution, [status(thm)], [c_168, c_176])).
% 2.68/1.40  tff(c_189, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_144])).
% 2.68/1.40  tff(c_46, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.68/1.40  tff(c_34, plain, (![A_22]: (k1_tops_1(A_22, k2_struct_0(A_22))=k2_struct_0(A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.40  tff(c_285, plain, (![C_88, A_89, B_90]: (m2_connsp_2(C_88, A_89, B_90) | ~r1_tarski(B_90, k1_tops_1(A_89, C_88)) | ~m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.68/1.40  tff(c_421, plain, (![A_107, B_108]: (m2_connsp_2(k2_struct_0(A_107), A_107, B_108) | ~r1_tarski(B_108, k2_struct_0(A_107)) | ~m1_subset_1(k2_struct_0(A_107), k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107))), inference(superposition, [status(thm), theory('equality')], [c_34, c_285])).
% 2.68/1.40  tff(c_423, plain, (![B_108]: (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', B_108) | ~r1_tarski(B_108, k2_struct_0('#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_421])).
% 2.68/1.40  tff(c_426, plain, (![B_109]: (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', B_109) | ~r1_tarski(B_109, k2_struct_0('#skF_4')) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_46, c_44, c_77, c_49, c_423])).
% 2.68/1.40  tff(c_429, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5') | ~r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_426])).
% 2.68/1.40  tff(c_436, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_429])).
% 2.68/1.40  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_436])).
% 2.68/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.40  
% 2.68/1.40  Inference rules
% 2.68/1.40  ----------------------
% 2.68/1.40  #Ref     : 0
% 2.68/1.40  #Sup     : 80
% 2.68/1.40  #Fact    : 0
% 2.68/1.40  #Define  : 0
% 2.68/1.40  #Split   : 3
% 2.68/1.40  #Chain   : 0
% 2.68/1.40  #Close   : 0
% 2.68/1.40  
% 2.68/1.40  Ordering : KBO
% 2.68/1.40  
% 2.68/1.40  Simplification rules
% 2.68/1.40  ----------------------
% 2.68/1.40  #Subsume      : 6
% 2.68/1.40  #Demod        : 45
% 2.68/1.40  #Tautology    : 23
% 2.68/1.40  #SimpNegUnit  : 1
% 2.68/1.40  #BackRed      : 1
% 2.68/1.40  
% 2.68/1.40  #Partial instantiations: 0
% 2.68/1.40  #Strategies tried      : 1
% 2.68/1.40  
% 2.68/1.40  Timing (in seconds)
% 2.68/1.40  ----------------------
% 2.68/1.40  Preprocessing        : 0.32
% 2.68/1.40  Parsing              : 0.17
% 2.68/1.40  CNF conversion       : 0.02
% 2.68/1.40  Main loop            : 0.28
% 2.68/1.40  Inferencing          : 0.11
% 2.68/1.40  Reduction            : 0.08
% 2.68/1.40  Demodulation         : 0.06
% 2.68/1.40  BG Simplification    : 0.02
% 2.68/1.40  Subsumption          : 0.06
% 2.68/1.41  Abstraction          : 0.02
% 2.68/1.41  MUC search           : 0.00
% 2.68/1.41  Cooper               : 0.00
% 2.68/1.41  Total                : 0.64
% 2.68/1.41  Index Insertion      : 0.00
% 2.68/1.41  Index Deletion       : 0.00
% 2.68/1.41  Index Matching       : 0.00
% 2.68/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
