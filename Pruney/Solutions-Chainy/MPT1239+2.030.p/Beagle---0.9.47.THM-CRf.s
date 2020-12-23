%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:44 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 102 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  101 ( 195 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_251,plain,(
    ! [A_100,B_101,C_102] :
      ( k7_subset_1(A_100,B_101,C_102) = k4_xboole_0(B_101,C_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_256,plain,(
    ! [C_102] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_102) = k4_xboole_0('#skF_2',C_102) ),
    inference(resolution,[status(thm)],[c_34,c_251])).

tff(c_338,plain,(
    ! [A_129,B_130,C_131] :
      ( m1_subset_1(k7_subset_1(A_129,B_130,C_131),k1_zfmisc_1(A_129))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_346,plain,(
    ! [C_102] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_102),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_338])).

tff(c_351,plain,(
    ! [C_102] : m1_subset_1(k4_xboole_0('#skF_2',C_102),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_346])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_tarski(k1_tops_1(A_29,B_33),k1_tops_1(A_29,C_35))
      | ~ r1_tarski(B_33,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_616,plain,(
    ! [A_196,B_197] :
      ( r1_tarski(k1_tops_1(A_196,B_197),B_197)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_631,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_616])).

tff(c_650,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_631])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_658,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_650,c_4])).

tff(c_622,plain,(
    ! [C_102] :
      ( r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_102)),k4_xboole_0('#skF_2',C_102))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_351,c_616])).

tff(c_854,plain,(
    ! [C_208] : r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_208)),k4_xboole_0('#skF_2',C_208)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_622])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_xboole_0(A_50,B_51)
      | ~ r1_xboole_0(A_50,k2_xboole_0(B_51,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_72,plain,(
    ! [A_13,B_51,C_52] : r1_xboole_0(k4_xboole_0(A_13,k2_xboole_0(B_51,C_52)),B_51) ),
    inference(resolution,[status(thm)],[c_16,c_64])).

tff(c_112,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_xboole_0(A_65,C_66)
      | ~ r1_xboole_0(B_67,C_66)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_123,plain,(
    ! [A_65,B_51,A_13,C_52] :
      ( r1_xboole_0(A_65,B_51)
      | ~ r1_tarski(A_65,k4_xboole_0(A_13,k2_xboole_0(B_51,C_52))) ) ),
    inference(resolution,[status(thm)],[c_72,c_112])).

tff(c_981,plain,(
    ! [B_225,C_226] : r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',k2_xboole_0(B_225,C_226))),B_225) ),
    inference(resolution,[status(thm)],[c_854,c_123])).

tff(c_994,plain,(
    r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_981])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(A_15,k4_xboole_0(B_16,C_17))
      | ~ r1_xboole_0(A_15,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_835,plain,(
    ! [A_204,B_205] :
      ( m1_subset_1(k1_tops_1(A_204,B_205),k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] :
      ( k7_subset_1(A_21,B_22,C_23) = k4_xboole_0(B_22,C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1718,plain,(
    ! [A_310,B_311,C_312] :
      ( k7_subset_1(u1_struct_0(A_310),k1_tops_1(A_310,B_311),C_312) = k4_xboole_0(k1_tops_1(A_310,B_311),C_312)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_pre_topc(A_310) ) ),
    inference(resolution,[status(thm)],[c_835,c_22])).

tff(c_1733,plain,(
    ! [C_312] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_312) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_312)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_1718])).

tff(c_1752,plain,(
    ! [C_312] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_312) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_312) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1733])).

tff(c_30,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_258,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_30])).

tff(c_1823,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_258])).

tff(c_2306,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_1823])).

tff(c_2309,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_994,c_2306])).

tff(c_2312,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2309])).

tff(c_2316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_351,c_34,c_6,c_2312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:26:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.88  
% 4.85/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.88  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.85/1.88  
% 4.85/1.88  %Foreground sorts:
% 4.85/1.88  
% 4.85/1.88  
% 4.85/1.88  %Background operators:
% 4.85/1.88  
% 4.85/1.88  
% 4.85/1.88  %Foreground operators:
% 4.85/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.85/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.85/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.85/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.85/1.88  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.85/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.85/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.85/1.88  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.85/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.85/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.85/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.85/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/1.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.85/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.85/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.85/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.85/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.85/1.88  
% 4.85/1.90  tff(f_109, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 4.85/1.90  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.85/1.90  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.85/1.90  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.85/1.90  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 4.85/1.90  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.85/1.90  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.85/1.90  tff(f_57, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.85/1.90  tff(f_55, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.85/1.90  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.85/1.90  tff(f_63, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 4.85/1.90  tff(f_77, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.85/1.90  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.85/1.90  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.85/1.90  tff(c_251, plain, (![A_100, B_101, C_102]: (k7_subset_1(A_100, B_101, C_102)=k4_xboole_0(B_101, C_102) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.85/1.90  tff(c_256, plain, (![C_102]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_102)=k4_xboole_0('#skF_2', C_102))), inference(resolution, [status(thm)], [c_34, c_251])).
% 4.85/1.90  tff(c_338, plain, (![A_129, B_130, C_131]: (m1_subset_1(k7_subset_1(A_129, B_130, C_131), k1_zfmisc_1(A_129)) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.85/1.90  tff(c_346, plain, (![C_102]: (m1_subset_1(k4_xboole_0('#skF_2', C_102), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_256, c_338])).
% 4.85/1.90  tff(c_351, plain, (![C_102]: (m1_subset_1(k4_xboole_0('#skF_2', C_102), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_346])).
% 4.85/1.90  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.85/1.90  tff(c_28, plain, (![A_29, B_33, C_35]: (r1_tarski(k1_tops_1(A_29, B_33), k1_tops_1(A_29, C_35)) | ~r1_tarski(B_33, C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.85/1.90  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.85/1.90  tff(c_616, plain, (![A_196, B_197]: (r1_tarski(k1_tops_1(A_196, B_197), B_197) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.85/1.90  tff(c_631, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_616])).
% 4.85/1.90  tff(c_650, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_631])).
% 4.85/1.90  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.85/1.90  tff(c_658, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_650, c_4])).
% 4.85/1.90  tff(c_622, plain, (![C_102]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_102)), k4_xboole_0('#skF_2', C_102)) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_351, c_616])).
% 4.85/1.90  tff(c_854, plain, (![C_208]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_208)), k4_xboole_0('#skF_2', C_208)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_622])).
% 4.85/1.90  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.85/1.90  tff(c_64, plain, (![A_50, B_51, C_52]: (r1_xboole_0(A_50, B_51) | ~r1_xboole_0(A_50, k2_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.85/1.90  tff(c_72, plain, (![A_13, B_51, C_52]: (r1_xboole_0(k4_xboole_0(A_13, k2_xboole_0(B_51, C_52)), B_51))), inference(resolution, [status(thm)], [c_16, c_64])).
% 4.85/1.90  tff(c_112, plain, (![A_65, C_66, B_67]: (r1_xboole_0(A_65, C_66) | ~r1_xboole_0(B_67, C_66) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.85/1.90  tff(c_123, plain, (![A_65, B_51, A_13, C_52]: (r1_xboole_0(A_65, B_51) | ~r1_tarski(A_65, k4_xboole_0(A_13, k2_xboole_0(B_51, C_52))))), inference(resolution, [status(thm)], [c_72, c_112])).
% 4.85/1.90  tff(c_981, plain, (![B_225, C_226]: (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', k2_xboole_0(B_225, C_226))), B_225))), inference(resolution, [status(thm)], [c_854, c_123])).
% 4.85/1.90  tff(c_994, plain, (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_658, c_981])).
% 4.85/1.90  tff(c_18, plain, (![A_15, B_16, C_17]: (r1_tarski(A_15, k4_xboole_0(B_16, C_17)) | ~r1_xboole_0(A_15, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.85/1.90  tff(c_835, plain, (![A_204, B_205]: (m1_subset_1(k1_tops_1(A_204, B_205), k1_zfmisc_1(u1_struct_0(A_204))) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.85/1.90  tff(c_22, plain, (![A_21, B_22, C_23]: (k7_subset_1(A_21, B_22, C_23)=k4_xboole_0(B_22, C_23) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.85/1.90  tff(c_1718, plain, (![A_310, B_311, C_312]: (k7_subset_1(u1_struct_0(A_310), k1_tops_1(A_310, B_311), C_312)=k4_xboole_0(k1_tops_1(A_310, B_311), C_312) | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_pre_topc(A_310))), inference(resolution, [status(thm)], [c_835, c_22])).
% 4.85/1.90  tff(c_1733, plain, (![C_312]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_312)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_312) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_1718])).
% 4.85/1.90  tff(c_1752, plain, (![C_312]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_312)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_312))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1733])).
% 4.85/1.90  tff(c_30, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.85/1.90  tff(c_258, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_30])).
% 4.85/1.90  tff(c_1823, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1752, c_258])).
% 4.85/1.90  tff(c_2306, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_1823])).
% 4.85/1.90  tff(c_2309, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_994, c_2306])).
% 4.85/1.90  tff(c_2312, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2309])).
% 4.85/1.90  tff(c_2316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_351, c_34, c_6, c_2312])).
% 4.85/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.90  
% 4.85/1.90  Inference rules
% 4.85/1.90  ----------------------
% 4.85/1.90  #Ref     : 0
% 4.85/1.90  #Sup     : 551
% 4.85/1.90  #Fact    : 0
% 4.85/1.90  #Define  : 0
% 4.85/1.90  #Split   : 2
% 4.85/1.90  #Chain   : 0
% 4.85/1.90  #Close   : 0
% 4.85/1.90  
% 4.85/1.90  Ordering : KBO
% 4.85/1.90  
% 4.85/1.90  Simplification rules
% 4.85/1.90  ----------------------
% 4.85/1.90  #Subsume      : 36
% 4.85/1.90  #Demod        : 205
% 4.85/1.90  #Tautology    : 161
% 4.85/1.90  #SimpNegUnit  : 0
% 4.85/1.90  #BackRed      : 2
% 4.85/1.90  
% 4.85/1.90  #Partial instantiations: 0
% 4.85/1.90  #Strategies tried      : 1
% 4.85/1.90  
% 4.85/1.90  Timing (in seconds)
% 4.85/1.90  ----------------------
% 4.85/1.90  Preprocessing        : 0.30
% 4.85/1.90  Parsing              : 0.17
% 4.85/1.90  CNF conversion       : 0.02
% 4.85/1.90  Main loop            : 0.83
% 4.85/1.90  Inferencing          : 0.26
% 4.85/1.90  Reduction            : 0.31
% 4.85/1.90  Demodulation         : 0.24
% 4.85/1.90  BG Simplification    : 0.03
% 4.85/1.90  Subsumption          : 0.17
% 4.85/1.90  Abstraction          : 0.03
% 4.85/1.90  MUC search           : 0.00
% 4.85/1.90  Cooper               : 0.00
% 4.85/1.90  Total                : 1.17
% 4.85/1.90  Index Insertion      : 0.00
% 4.85/1.90  Index Deletion       : 0.00
% 4.85/1.90  Index Matching       : 0.00
% 4.85/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
