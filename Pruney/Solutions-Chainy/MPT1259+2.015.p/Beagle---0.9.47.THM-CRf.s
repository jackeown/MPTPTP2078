%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:00 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   50 (  64 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 141 expanded)
%              Number of equality atoms :   31 (  36 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k2_tops_1(A,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_tops_1(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_22,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_106,plain,(
    ! [A_40,B_41] :
      ( k1_tops_1(A_40,k2_tops_1(A_40,k2_tops_1(A_40,B_41))) = k1_xboole_0
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_110,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_114,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_110])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k2_tops_1(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_119,plain,(
    ! [A_42,B_43] :
      ( k7_subset_1(u1_struct_0(A_42),B_43,k2_tops_1(A_42,B_43)) = k1_tops_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_124,plain,(
    ! [A_8,B_9] :
      ( k7_subset_1(u1_struct_0(A_8),k2_tops_1(A_8,B_9),k2_tops_1(A_8,k2_tops_1(A_8,B_9))) = k1_tops_1(A_8,k2_tops_1(A_8,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_119])).

tff(c_90,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k2_tops_1(A_36,B_37),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( k7_subset_1(A_5,B_6,C_7) = k4_xboole_0(B_6,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_46,B_47,C_48] :
      ( k7_subset_1(u1_struct_0(A_46),k2_tops_1(A_46,B_47),C_48) = k4_xboole_0(k2_tops_1(A_46,B_47),C_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_90,c_12])).

tff(c_202,plain,(
    ! [A_54,B_55,C_56] :
      ( k7_subset_1(u1_struct_0(A_54),k2_tops_1(A_54,k2_tops_1(A_54,B_55)),C_56) = k4_xboole_0(k2_tops_1(A_54,k2_tops_1(A_54,B_55)),C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_14,c_147])).

tff(c_261,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(k2_tops_1(A_61,k2_tops_1(A_61,B_62)),k2_tops_1(A_61,k2_tops_1(A_61,k2_tops_1(A_61,B_62)))) = k1_tops_1(A_61,k2_tops_1(A_61,k2_tops_1(A_61,B_62)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ m1_subset_1(k2_tops_1(A_61,B_62),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_202])).

tff(c_94,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k2_tops_1(A_38,k2_tops_1(A_38,B_39)),k2_tops_1(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_103,plain,(
    ! [A_38,B_39] :
      ( k2_tops_1(A_38,k2_tops_1(A_38,B_39)) = k2_tops_1(A_38,B_39)
      | k4_xboole_0(k2_tops_1(A_38,B_39),k2_tops_1(A_38,k2_tops_1(A_38,B_39))) != k1_xboole_0
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_94,c_53])).

tff(c_275,plain,(
    ! [A_63,B_64] :
      ( k2_tops_1(A_63,k2_tops_1(A_63,k2_tops_1(A_63,B_64))) = k2_tops_1(A_63,k2_tops_1(A_63,B_64))
      | k1_tops_1(A_63,k2_tops_1(A_63,k2_tops_1(A_63,B_64))) != k1_xboole_0
      | ~ m1_subset_1(k2_tops_1(A_63,B_64),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ m1_subset_1(k2_tops_1(A_63,B_64),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_103])).

tff(c_279,plain,(
    ! [A_65,B_66] :
      ( k2_tops_1(A_65,k2_tops_1(A_65,k2_tops_1(A_65,B_66))) = k2_tops_1(A_65,k2_tops_1(A_65,B_66))
      | k1_tops_1(A_65,k2_tops_1(A_65,k2_tops_1(A_65,B_66))) != k1_xboole_0
      | ~ m1_subset_1(k2_tops_1(A_65,B_66),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_14,c_275])).

tff(c_283,plain,(
    ! [A_67,B_68] :
      ( k2_tops_1(A_67,k2_tops_1(A_67,k2_tops_1(A_67,B_68))) = k2_tops_1(A_67,k2_tops_1(A_67,B_68))
      | k1_tops_1(A_67,k2_tops_1(A_67,k2_tops_1(A_67,B_68))) != k1_xboole_0
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_14,c_279])).

tff(c_287,plain,
    ( k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_283])).

tff(c_291,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_114,c_287])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:16:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.35  
% 2.29/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.36  %$ r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.29/1.36  
% 2.29/1.36  %Foreground sorts:
% 2.29/1.36  
% 2.29/1.36  
% 2.29/1.36  %Background operators:
% 2.29/1.36  
% 2.29/1.36  
% 2.29/1.36  %Foreground operators:
% 2.29/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.36  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.29/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.36  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.29/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.36  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.29/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.29/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.36  
% 2.47/1.37  tff(f_78, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k2_tops_1(A, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tops_1)).
% 2.47/1.37  tff(f_54, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l80_tops_1)).
% 2.47/1.37  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.47/1.37  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 2.47/1.37  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.47/1.37  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_tops_1(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_tops_1)).
% 2.47/1.37  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.47/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.47/1.37  tff(c_22, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.37  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.37  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.37  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.37  tff(c_106, plain, (![A_40, B_41]: (k1_tops_1(A_40, k2_tops_1(A_40, k2_tops_1(A_40, B_41)))=k1_xboole_0 | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.37  tff(c_110, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_106])).
% 2.47/1.37  tff(c_114, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_110])).
% 2.47/1.37  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(k2_tops_1(A_8, B_9), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.37  tff(c_119, plain, (![A_42, B_43]: (k7_subset_1(u1_struct_0(A_42), B_43, k2_tops_1(A_42, B_43))=k1_tops_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.37  tff(c_124, plain, (![A_8, B_9]: (k7_subset_1(u1_struct_0(A_8), k2_tops_1(A_8, B_9), k2_tops_1(A_8, k2_tops_1(A_8, B_9)))=k1_tops_1(A_8, k2_tops_1(A_8, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_14, c_119])).
% 2.47/1.37  tff(c_90, plain, (![A_36, B_37]: (m1_subset_1(k2_tops_1(A_36, B_37), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.37  tff(c_12, plain, (![A_5, B_6, C_7]: (k7_subset_1(A_5, B_6, C_7)=k4_xboole_0(B_6, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/1.37  tff(c_147, plain, (![A_46, B_47, C_48]: (k7_subset_1(u1_struct_0(A_46), k2_tops_1(A_46, B_47), C_48)=k4_xboole_0(k2_tops_1(A_46, B_47), C_48) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_90, c_12])).
% 2.47/1.37  tff(c_202, plain, (![A_54, B_55, C_56]: (k7_subset_1(u1_struct_0(A_54), k2_tops_1(A_54, k2_tops_1(A_54, B_55)), C_56)=k4_xboole_0(k2_tops_1(A_54, k2_tops_1(A_54, B_55)), C_56) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_14, c_147])).
% 2.47/1.37  tff(c_261, plain, (![A_61, B_62]: (k4_xboole_0(k2_tops_1(A_61, k2_tops_1(A_61, B_62)), k2_tops_1(A_61, k2_tops_1(A_61, k2_tops_1(A_61, B_62))))=k1_tops_1(A_61, k2_tops_1(A_61, k2_tops_1(A_61, B_62))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~m1_subset_1(k2_tops_1(A_61, B_62), k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(superposition, [status(thm), theory('equality')], [c_124, c_202])).
% 2.47/1.37  tff(c_94, plain, (![A_38, B_39]: (r1_tarski(k2_tops_1(A_38, k2_tops_1(A_38, B_39)), k2_tops_1(A_38, B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.47/1.37  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.37  tff(c_48, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.37  tff(c_53, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_48])).
% 2.47/1.37  tff(c_103, plain, (![A_38, B_39]: (k2_tops_1(A_38, k2_tops_1(A_38, B_39))=k2_tops_1(A_38, B_39) | k4_xboole_0(k2_tops_1(A_38, B_39), k2_tops_1(A_38, k2_tops_1(A_38, B_39)))!=k1_xboole_0 | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_94, c_53])).
% 2.47/1.37  tff(c_275, plain, (![A_63, B_64]: (k2_tops_1(A_63, k2_tops_1(A_63, k2_tops_1(A_63, B_64)))=k2_tops_1(A_63, k2_tops_1(A_63, B_64)) | k1_tops_1(A_63, k2_tops_1(A_63, k2_tops_1(A_63, B_64)))!=k1_xboole_0 | ~m1_subset_1(k2_tops_1(A_63, B_64), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~m1_subset_1(k2_tops_1(A_63, B_64), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(superposition, [status(thm), theory('equality')], [c_261, c_103])).
% 2.47/1.37  tff(c_279, plain, (![A_65, B_66]: (k2_tops_1(A_65, k2_tops_1(A_65, k2_tops_1(A_65, B_66)))=k2_tops_1(A_65, k2_tops_1(A_65, B_66)) | k1_tops_1(A_65, k2_tops_1(A_65, k2_tops_1(A_65, B_66)))!=k1_xboole_0 | ~m1_subset_1(k2_tops_1(A_65, B_66), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_14, c_275])).
% 2.47/1.37  tff(c_283, plain, (![A_67, B_68]: (k2_tops_1(A_67, k2_tops_1(A_67, k2_tops_1(A_67, B_68)))=k2_tops_1(A_67, k2_tops_1(A_67, B_68)) | k1_tops_1(A_67, k2_tops_1(A_67, k2_tops_1(A_67, B_68)))!=k1_xboole_0 | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_14, c_279])).
% 2.47/1.37  tff(c_287, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_283])).
% 2.47/1.37  tff(c_291, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_114, c_287])).
% 2.47/1.37  tff(c_293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_291])).
% 2.47/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  Inference rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Ref     : 0
% 2.47/1.37  #Sup     : 61
% 2.47/1.37  #Fact    : 0
% 2.47/1.37  #Define  : 0
% 2.47/1.37  #Split   : 3
% 2.47/1.37  #Chain   : 0
% 2.47/1.37  #Close   : 0
% 2.47/1.37  
% 2.47/1.37  Ordering : KBO
% 2.47/1.37  
% 2.47/1.37  Simplification rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Subsume      : 7
% 2.47/1.37  #Demod        : 25
% 2.47/1.37  #Tautology    : 32
% 2.47/1.37  #SimpNegUnit  : 1
% 2.47/1.37  #BackRed      : 0
% 2.47/1.37  
% 2.47/1.37  #Partial instantiations: 0
% 2.47/1.37  #Strategies tried      : 1
% 2.47/1.37  
% 2.47/1.37  Timing (in seconds)
% 2.47/1.37  ----------------------
% 2.47/1.37  Preprocessing        : 0.32
% 2.47/1.37  Parsing              : 0.18
% 2.47/1.37  CNF conversion       : 0.02
% 2.47/1.37  Main loop            : 0.25
% 2.47/1.37  Inferencing          : 0.09
% 2.47/1.37  Reduction            : 0.07
% 2.47/1.37  Demodulation         : 0.05
% 2.47/1.37  BG Simplification    : 0.01
% 2.47/1.38  Subsumption          : 0.05
% 2.47/1.38  Abstraction          : 0.02
% 2.47/1.38  MUC search           : 0.00
% 2.47/1.38  Cooper               : 0.00
% 2.47/1.38  Total                : 0.60
% 2.47/1.38  Index Insertion      : 0.00
% 2.47/1.38  Index Deletion       : 0.00
% 2.47/1.38  Index Matching       : 0.00
% 2.47/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
