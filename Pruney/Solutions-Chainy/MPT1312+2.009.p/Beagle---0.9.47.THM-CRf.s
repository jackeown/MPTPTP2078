%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:58 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 184 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 360 expanded)
%              Number of equality atoms :   14 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_35,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_41,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_45,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_26,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_26])).

tff(c_56,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ~ r1_tarski('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_46])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_65,plain,(
    ! [B_37,A_38] :
      ( l1_pre_topc(B_37)
      | ~ m1_pre_topc(B_37,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_71,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_68])).

tff(c_39,plain,(
    ! [A_12] :
      ( u1_struct_0(A_12) = k2_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_75,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_39])).

tff(c_88,plain,(
    ! [A_41] :
      ( m1_subset_1(k2_struct_0(A_41),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_99,plain,(
    ! [A_42] :
      ( r1_tarski(k2_struct_0(A_42),u1_struct_0(A_42))
      | ~ l1_struct_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_88,c_12])).

tff(c_102,plain,
    ( r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_99])).

tff(c_106,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_109,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_106])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_109])).

tff(c_114,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_238,plain,(
    ! [C_61,A_62,B_63] :
      ( m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0(B_63)))
      | ~ m1_pre_topc(B_63,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_268,plain,(
    ! [A_66,A_67,B_68] :
      ( m1_subset_1(A_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_pre_topc(B_68,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ r1_tarski(A_66,u1_struct_0(B_68)) ) ),
    inference(resolution,[status(thm)],[c_14,c_238])).

tff(c_270,plain,(
    ! [A_66] :
      ( m1_subset_1(A_66,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_66,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_30,c_268])).

tff(c_274,plain,(
    ! [A_69] :
      ( m1_subset_1(A_69,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_69,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_32,c_45,c_270])).

tff(c_279,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,k2_struct_0('#skF_1'))
      | ~ r1_tarski(A_70,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_274,c_12])).

tff(c_283,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_114,c_279])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_zfmisc_1(A_6),k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_55,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_76,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_55])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [A_45,C_46,B_47] :
      ( r2_xboole_0(A_45,C_46)
      | ~ r2_xboole_0(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_166,plain,(
    ! [A_48,B_49,A_50] :
      ( r2_xboole_0(A_48,B_49)
      | ~ r1_tarski(A_48,A_50)
      | B_49 = A_50
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_2,c_162])).

tff(c_182,plain,(
    ! [B_51] :
      ( r2_xboole_0('#skF_3',B_51)
      | k1_zfmisc_1(k2_struct_0('#skF_2')) = B_51
      | ~ r1_tarski(k1_zfmisc_1(k2_struct_0('#skF_2')),B_51) ) ),
    inference(resolution,[status(thm)],[c_76,c_166])).

tff(c_201,plain,(
    ! [B_54] :
      ( r2_xboole_0('#skF_3',k1_zfmisc_1(B_54))
      | k1_zfmisc_1(k2_struct_0('#skF_2')) = k1_zfmisc_1(B_54)
      | ~ r1_tarski(k2_struct_0('#skF_2'),B_54) ) ),
    inference(resolution,[status(thm)],[c_10,c_182])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_208,plain,(
    ! [B_54] :
      ( r1_tarski('#skF_3',k1_zfmisc_1(B_54))
      | k1_zfmisc_1(k2_struct_0('#skF_2')) = k1_zfmisc_1(B_54)
      | ~ r1_tarski(k2_struct_0('#skF_2'),B_54) ) ),
    inference(resolution,[status(thm)],[c_201,c_6])).

tff(c_286,plain,
    ( r1_tarski('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | k1_zfmisc_1(k2_struct_0('#skF_2')) = k1_zfmisc_1(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_283,c_208])).

tff(c_291,plain,(
    k1_zfmisc_1(k2_struct_0('#skF_2')) = k1_zfmisc_1(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_286])).

tff(c_77,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_28])).

tff(c_315,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_77])).

tff(c_318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:08:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.33  
% 2.47/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.33  %$ r2_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.47/1.33  
% 2.47/1.33  %Foreground sorts:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Background operators:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Foreground operators:
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.47/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.33  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.47/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.47/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.47/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.33  
% 2.47/1.35  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 2.47/1.35  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.47/1.35  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.47/1.35  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.47/1.35  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.47/1.35  tff(f_54, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.47/1.35  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.47/1.35  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.47/1.35  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.47/1.35  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l58_xboole_1)).
% 2.47/1.35  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.47/1.35  tff(c_20, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.47/1.35  tff(c_35, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.47/1.35  tff(c_41, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_20, c_35])).
% 2.47/1.35  tff(c_45, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_41])).
% 2.47/1.35  tff(c_26, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.47/1.35  tff(c_46, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_26])).
% 2.47/1.35  tff(c_56, plain, (![A_35, B_36]: (m1_subset_1(A_35, k1_zfmisc_1(B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.35  tff(c_64, plain, (~r1_tarski('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_56, c_46])).
% 2.47/1.35  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.47/1.35  tff(c_65, plain, (![B_37, A_38]: (l1_pre_topc(B_37) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.35  tff(c_68, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_65])).
% 2.47/1.35  tff(c_71, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_68])).
% 2.47/1.35  tff(c_39, plain, (![A_12]: (u1_struct_0(A_12)=k2_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_20, c_35])).
% 2.47/1.35  tff(c_75, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_71, c_39])).
% 2.47/1.35  tff(c_88, plain, (![A_41]: (m1_subset_1(k2_struct_0(A_41), k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.35  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.35  tff(c_99, plain, (![A_42]: (r1_tarski(k2_struct_0(A_42), u1_struct_0(A_42)) | ~l1_struct_0(A_42))), inference(resolution, [status(thm)], [c_88, c_12])).
% 2.47/1.35  tff(c_102, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_75, c_99])).
% 2.47/1.35  tff(c_106, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_102])).
% 2.47/1.35  tff(c_109, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_106])).
% 2.47/1.35  tff(c_113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_109])).
% 2.47/1.35  tff(c_114, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_102])).
% 2.47/1.35  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.35  tff(c_238, plain, (![C_61, A_62, B_63]: (m1_subset_1(C_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(C_61, k1_zfmisc_1(u1_struct_0(B_63))) | ~m1_pre_topc(B_63, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.47/1.35  tff(c_268, plain, (![A_66, A_67, B_68]: (m1_subset_1(A_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_pre_topc(B_68, A_67) | ~l1_pre_topc(A_67) | ~r1_tarski(A_66, u1_struct_0(B_68)))), inference(resolution, [status(thm)], [c_14, c_238])).
% 2.47/1.35  tff(c_270, plain, (![A_66]: (m1_subset_1(A_66, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_66, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_30, c_268])).
% 2.47/1.35  tff(c_274, plain, (![A_69]: (m1_subset_1(A_69, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_69, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_32, c_45, c_270])).
% 2.47/1.35  tff(c_279, plain, (![A_70]: (r1_tarski(A_70, k2_struct_0('#skF_1')) | ~r1_tarski(A_70, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_274, c_12])).
% 2.47/1.35  tff(c_283, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_114, c_279])).
% 2.47/1.35  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_zfmisc_1(A_6), k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.47/1.35  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.47/1.35  tff(c_51, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.35  tff(c_55, plain, (r1_tarski('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_51])).
% 2.47/1.35  tff(c_76, plain, (r1_tarski('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_55])).
% 2.47/1.35  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.35  tff(c_162, plain, (![A_45, C_46, B_47]: (r2_xboole_0(A_45, C_46) | ~r2_xboole_0(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.47/1.35  tff(c_166, plain, (![A_48, B_49, A_50]: (r2_xboole_0(A_48, B_49) | ~r1_tarski(A_48, A_50) | B_49=A_50 | ~r1_tarski(A_50, B_49))), inference(resolution, [status(thm)], [c_2, c_162])).
% 2.47/1.35  tff(c_182, plain, (![B_51]: (r2_xboole_0('#skF_3', B_51) | k1_zfmisc_1(k2_struct_0('#skF_2'))=B_51 | ~r1_tarski(k1_zfmisc_1(k2_struct_0('#skF_2')), B_51))), inference(resolution, [status(thm)], [c_76, c_166])).
% 2.47/1.35  tff(c_201, plain, (![B_54]: (r2_xboole_0('#skF_3', k1_zfmisc_1(B_54)) | k1_zfmisc_1(k2_struct_0('#skF_2'))=k1_zfmisc_1(B_54) | ~r1_tarski(k2_struct_0('#skF_2'), B_54))), inference(resolution, [status(thm)], [c_10, c_182])).
% 2.47/1.35  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.35  tff(c_208, plain, (![B_54]: (r1_tarski('#skF_3', k1_zfmisc_1(B_54)) | k1_zfmisc_1(k2_struct_0('#skF_2'))=k1_zfmisc_1(B_54) | ~r1_tarski(k2_struct_0('#skF_2'), B_54))), inference(resolution, [status(thm)], [c_201, c_6])).
% 2.47/1.35  tff(c_286, plain, (r1_tarski('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1'))) | k1_zfmisc_1(k2_struct_0('#skF_2'))=k1_zfmisc_1(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_283, c_208])).
% 2.47/1.35  tff(c_291, plain, (k1_zfmisc_1(k2_struct_0('#skF_2'))=k1_zfmisc_1(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_286])).
% 2.47/1.35  tff(c_77, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_28])).
% 2.47/1.35  tff(c_315, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_77])).
% 2.47/1.35  tff(c_318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_315])).
% 2.47/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  Inference rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Ref     : 0
% 2.47/1.35  #Sup     : 59
% 2.47/1.35  #Fact    : 0
% 2.47/1.35  #Define  : 0
% 2.47/1.35  #Split   : 3
% 2.47/1.35  #Chain   : 0
% 2.47/1.35  #Close   : 0
% 2.47/1.35  
% 2.47/1.35  Ordering : KBO
% 2.47/1.35  
% 2.47/1.35  Simplification rules
% 2.47/1.35  ----------------------
% 2.47/1.35  #Subsume      : 3
% 2.47/1.35  #Demod        : 36
% 2.47/1.35  #Tautology    : 17
% 2.47/1.35  #SimpNegUnit  : 2
% 2.47/1.35  #BackRed      : 9
% 2.47/1.35  
% 2.47/1.35  #Partial instantiations: 0
% 2.47/1.35  #Strategies tried      : 1
% 2.47/1.35  
% 2.47/1.35  Timing (in seconds)
% 2.47/1.35  ----------------------
% 2.47/1.35  Preprocessing        : 0.32
% 2.47/1.35  Parsing              : 0.17
% 2.47/1.35  CNF conversion       : 0.02
% 2.47/1.35  Main loop            : 0.25
% 2.47/1.35  Inferencing          : 0.09
% 2.47/1.35  Reduction            : 0.07
% 2.47/1.35  Demodulation         : 0.05
% 2.47/1.35  BG Simplification    : 0.01
% 2.47/1.35  Subsumption          : 0.05
% 2.47/1.35  Abstraction          : 0.01
% 2.47/1.35  MUC search           : 0.00
% 2.47/1.35  Cooper               : 0.00
% 2.47/1.35  Total                : 0.61
% 2.47/1.35  Index Insertion      : 0.00
% 2.47/1.35  Index Deletion       : 0.00
% 2.47/1.35  Index Matching       : 0.00
% 2.47/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
