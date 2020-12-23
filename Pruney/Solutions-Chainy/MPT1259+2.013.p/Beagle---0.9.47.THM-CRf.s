%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:00 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   58 (  79 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 189 expanded)
%              Number of equality atoms :   37 (  46 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k2_tops_1(A,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

tff(f_62,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_78,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_24,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_115,plain,(
    ! [A_44,B_45] :
      ( k1_tops_1(A_44,k2_tops_1(A_44,k2_tops_1(A_44,B_45))) = k1_xboole_0
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_119,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_115])).

tff(c_123,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_119])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k2_tops_1(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [A_40,B_41] :
      ( v4_pre_topc(k2_tops_1(A_40,B_41),A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,(
    ! [A_8,B_9] :
      ( v4_pre_topc(k2_tops_1(A_8,k2_tops_1(A_8,B_9)),A_8)
      | ~ v2_pre_topc(A_8)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_96])).

tff(c_105,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k2_tops_1(A_42,B_43),B_43)
      | ~ v4_pre_topc(B_43,A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_172,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k2_tops_1(A_56,k2_tops_1(A_56,B_57)),k2_tops_1(A_56,B_57))
      | ~ v4_pre_topc(k2_tops_1(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_14,c_105])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_183,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(k2_tops_1(A_56,k2_tops_1(A_56,B_57)),k2_tops_1(A_56,B_57)) = k1_xboole_0
      | ~ v4_pre_topc(k2_tops_1(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_172,c_10])).

tff(c_129,plain,(
    ! [A_48,B_49] :
      ( k7_subset_1(u1_struct_0(A_48),B_49,k2_tops_1(A_48,B_49)) = k1_tops_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_134,plain,(
    ! [A_8,B_9] :
      ( k7_subset_1(u1_struct_0(A_8),k2_tops_1(A_8,B_9),k2_tops_1(A_8,k2_tops_1(A_8,B_9))) = k1_tops_1(A_8,k2_tops_1(A_8,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_129])).

tff(c_92,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k2_tops_1(A_38,B_39),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( k7_subset_1(A_5,B_6,C_7) = k4_xboole_0(B_6,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_154,plain,(
    ! [A_52,B_53,C_54] :
      ( k7_subset_1(u1_struct_0(A_52),k2_tops_1(A_52,B_53),C_54) = k4_xboole_0(k2_tops_1(A_52,B_53),C_54)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_92,c_12])).

tff(c_224,plain,(
    ! [A_62,B_63,C_64] :
      ( k7_subset_1(u1_struct_0(A_62),k2_tops_1(A_62,k2_tops_1(A_62,B_63)),C_64) = k4_xboole_0(k2_tops_1(A_62,k2_tops_1(A_62,B_63)),C_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_14,c_154])).

tff(c_283,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(k2_tops_1(A_69,k2_tops_1(A_69,B_70)),k2_tops_1(A_69,k2_tops_1(A_69,k2_tops_1(A_69,B_70)))) = k1_tops_1(A_69,k2_tops_1(A_69,k2_tops_1(A_69,B_70)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ m1_subset_1(k2_tops_1(A_69,B_70),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_224])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    ! [B_28,A_29] :
      ( B_28 = A_29
      | ~ r1_tarski(B_28,A_29)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | k4_xboole_0(A_31,B_30) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_50])).

tff(c_67,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | k4_xboole_0(B_4,A_3) != k1_xboole_0
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_60])).

tff(c_297,plain,(
    ! [A_71,B_72] :
      ( k2_tops_1(A_71,k2_tops_1(A_71,k2_tops_1(A_71,B_72))) = k2_tops_1(A_71,k2_tops_1(A_71,B_72))
      | k1_tops_1(A_71,k2_tops_1(A_71,k2_tops_1(A_71,B_72))) != k1_xboole_0
      | k4_xboole_0(k2_tops_1(A_71,k2_tops_1(A_71,k2_tops_1(A_71,B_72))),k2_tops_1(A_71,k2_tops_1(A_71,B_72))) != k1_xboole_0
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ m1_subset_1(k2_tops_1(A_71,B_72),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_67])).

tff(c_303,plain,(
    ! [A_73,B_74] :
      ( k2_tops_1(A_73,k2_tops_1(A_73,k2_tops_1(A_73,B_74))) = k2_tops_1(A_73,k2_tops_1(A_73,B_74))
      | k1_tops_1(A_73,k2_tops_1(A_73,k2_tops_1(A_73,B_74))) != k1_xboole_0
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ v4_pre_topc(k2_tops_1(A_73,k2_tops_1(A_73,B_74)),A_73)
      | ~ m1_subset_1(k2_tops_1(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_297])).

tff(c_307,plain,(
    ! [A_75,B_76] :
      ( k2_tops_1(A_75,k2_tops_1(A_75,k2_tops_1(A_75,B_76))) = k2_tops_1(A_75,k2_tops_1(A_75,B_76))
      | k1_tops_1(A_75,k2_tops_1(A_75,k2_tops_1(A_75,B_76))) != k1_xboole_0
      | ~ m1_subset_1(k2_tops_1(A_75,B_76),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ v2_pre_topc(A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_101,c_303])).

tff(c_311,plain,(
    ! [A_77,B_78] :
      ( k2_tops_1(A_77,k2_tops_1(A_77,k2_tops_1(A_77,B_78))) = k2_tops_1(A_77,k2_tops_1(A_77,B_78))
      | k1_tops_1(A_77,k2_tops_1(A_77,k2_tops_1(A_77,B_78))) != k1_xboole_0
      | ~ v2_pre_topc(A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_14,c_307])).

tff(c_315,plain,
    ( k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k1_xboole_0
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_311])).

tff(c_319,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_123,c_315])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:33:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.32  
% 2.38/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.32  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.38/1.32  
% 2.38/1.32  %Foreground sorts:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Background operators:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Foreground operators:
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.38/1.32  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.38/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.38/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.32  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.38/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.32  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.38/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.38/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.32  
% 2.66/1.33  tff(f_88, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k2_tops_1(A, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tops_1)).
% 2.66/1.33  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l80_tops_1)).
% 2.66/1.33  tff(f_45, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.66/1.33  tff(f_53, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_tops_1)).
% 2.66/1.33  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 2.66/1.33  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.66/1.33  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 2.66/1.33  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.66/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.66/1.33  tff(c_24, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.66/1.33  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.66/1.33  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.66/1.33  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.66/1.33  tff(c_115, plain, (![A_44, B_45]: (k1_tops_1(A_44, k2_tops_1(A_44, k2_tops_1(A_44, B_45)))=k1_xboole_0 | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.33  tff(c_119, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_115])).
% 2.66/1.33  tff(c_123, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_119])).
% 2.66/1.33  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(k2_tops_1(A_8, B_9), k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.66/1.33  tff(c_96, plain, (![A_40, B_41]: (v4_pre_topc(k2_tops_1(A_40, B_41), A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.33  tff(c_101, plain, (![A_8, B_9]: (v4_pre_topc(k2_tops_1(A_8, k2_tops_1(A_8, B_9)), A_8) | ~v2_pre_topc(A_8) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_14, c_96])).
% 2.66/1.33  tff(c_105, plain, (![A_42, B_43]: (r1_tarski(k2_tops_1(A_42, B_43), B_43) | ~v4_pre_topc(B_43, A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.66/1.33  tff(c_172, plain, (![A_56, B_57]: (r1_tarski(k2_tops_1(A_56, k2_tops_1(A_56, B_57)), k2_tops_1(A_56, B_57)) | ~v4_pre_topc(k2_tops_1(A_56, B_57), A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_14, c_105])).
% 2.66/1.33  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.33  tff(c_183, plain, (![A_56, B_57]: (k4_xboole_0(k2_tops_1(A_56, k2_tops_1(A_56, B_57)), k2_tops_1(A_56, B_57))=k1_xboole_0 | ~v4_pre_topc(k2_tops_1(A_56, B_57), A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_172, c_10])).
% 2.66/1.33  tff(c_129, plain, (![A_48, B_49]: (k7_subset_1(u1_struct_0(A_48), B_49, k2_tops_1(A_48, B_49))=k1_tops_1(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.66/1.33  tff(c_134, plain, (![A_8, B_9]: (k7_subset_1(u1_struct_0(A_8), k2_tops_1(A_8, B_9), k2_tops_1(A_8, k2_tops_1(A_8, B_9)))=k1_tops_1(A_8, k2_tops_1(A_8, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_14, c_129])).
% 2.66/1.33  tff(c_92, plain, (![A_38, B_39]: (m1_subset_1(k2_tops_1(A_38, B_39), k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.66/1.33  tff(c_12, plain, (![A_5, B_6, C_7]: (k7_subset_1(A_5, B_6, C_7)=k4_xboole_0(B_6, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.33  tff(c_154, plain, (![A_52, B_53, C_54]: (k7_subset_1(u1_struct_0(A_52), k2_tops_1(A_52, B_53), C_54)=k4_xboole_0(k2_tops_1(A_52, B_53), C_54) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_92, c_12])).
% 2.66/1.33  tff(c_224, plain, (![A_62, B_63, C_64]: (k7_subset_1(u1_struct_0(A_62), k2_tops_1(A_62, k2_tops_1(A_62, B_63)), C_64)=k4_xboole_0(k2_tops_1(A_62, k2_tops_1(A_62, B_63)), C_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_14, c_154])).
% 2.66/1.33  tff(c_283, plain, (![A_69, B_70]: (k4_xboole_0(k2_tops_1(A_69, k2_tops_1(A_69, B_70)), k2_tops_1(A_69, k2_tops_1(A_69, k2_tops_1(A_69, B_70))))=k1_tops_1(A_69, k2_tops_1(A_69, k2_tops_1(A_69, B_70))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~m1_subset_1(k2_tops_1(A_69, B_70), k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(superposition, [status(thm), theory('equality')], [c_134, c_224])).
% 2.66/1.33  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.33  tff(c_50, plain, (![B_28, A_29]: (B_28=A_29 | ~r1_tarski(B_28, A_29) | ~r1_tarski(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.33  tff(c_60, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | k4_xboole_0(A_31, B_30)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_50])).
% 2.66/1.33  tff(c_67, plain, (![B_4, A_3]: (B_4=A_3 | k4_xboole_0(B_4, A_3)!=k1_xboole_0 | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_60])).
% 2.66/1.33  tff(c_297, plain, (![A_71, B_72]: (k2_tops_1(A_71, k2_tops_1(A_71, k2_tops_1(A_71, B_72)))=k2_tops_1(A_71, k2_tops_1(A_71, B_72)) | k1_tops_1(A_71, k2_tops_1(A_71, k2_tops_1(A_71, B_72)))!=k1_xboole_0 | k4_xboole_0(k2_tops_1(A_71, k2_tops_1(A_71, k2_tops_1(A_71, B_72))), k2_tops_1(A_71, k2_tops_1(A_71, B_72)))!=k1_xboole_0 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~m1_subset_1(k2_tops_1(A_71, B_72), k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(superposition, [status(thm), theory('equality')], [c_283, c_67])).
% 2.66/1.33  tff(c_303, plain, (![A_73, B_74]: (k2_tops_1(A_73, k2_tops_1(A_73, k2_tops_1(A_73, B_74)))=k2_tops_1(A_73, k2_tops_1(A_73, B_74)) | k1_tops_1(A_73, k2_tops_1(A_73, k2_tops_1(A_73, B_74)))!=k1_xboole_0 | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~v4_pre_topc(k2_tops_1(A_73, k2_tops_1(A_73, B_74)), A_73) | ~m1_subset_1(k2_tops_1(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(superposition, [status(thm), theory('equality')], [c_183, c_297])).
% 2.66/1.33  tff(c_307, plain, (![A_75, B_76]: (k2_tops_1(A_75, k2_tops_1(A_75, k2_tops_1(A_75, B_76)))=k2_tops_1(A_75, k2_tops_1(A_75, B_76)) | k1_tops_1(A_75, k2_tops_1(A_75, k2_tops_1(A_75, B_76)))!=k1_xboole_0 | ~m1_subset_1(k2_tops_1(A_75, B_76), k1_zfmisc_1(u1_struct_0(A_75))) | ~v2_pre_topc(A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_101, c_303])).
% 2.66/1.33  tff(c_311, plain, (![A_77, B_78]: (k2_tops_1(A_77, k2_tops_1(A_77, k2_tops_1(A_77, B_78)))=k2_tops_1(A_77, k2_tops_1(A_77, B_78)) | k1_tops_1(A_77, k2_tops_1(A_77, k2_tops_1(A_77, B_78)))!=k1_xboole_0 | ~v2_pre_topc(A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_14, c_307])).
% 2.66/1.33  tff(c_315, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k1_xboole_0 | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_311])).
% 2.66/1.33  tff(c_319, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_123, c_315])).
% 2.66/1.33  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_319])).
% 2.66/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.33  
% 2.66/1.33  Inference rules
% 2.66/1.33  ----------------------
% 2.66/1.33  #Ref     : 0
% 2.66/1.33  #Sup     : 66
% 2.66/1.33  #Fact    : 0
% 2.66/1.33  #Define  : 0
% 2.66/1.33  #Split   : 4
% 2.66/1.33  #Chain   : 0
% 2.66/1.33  #Close   : 0
% 2.66/1.33  
% 2.66/1.33  Ordering : KBO
% 2.66/1.33  
% 2.66/1.33  Simplification rules
% 2.66/1.33  ----------------------
% 2.66/1.33  #Subsume      : 6
% 2.66/1.33  #Demod        : 33
% 2.66/1.33  #Tautology    : 32
% 2.66/1.33  #SimpNegUnit  : 1
% 2.66/1.33  #BackRed      : 0
% 2.66/1.33  
% 2.66/1.33  #Partial instantiations: 0
% 2.66/1.33  #Strategies tried      : 1
% 2.66/1.33  
% 2.66/1.33  Timing (in seconds)
% 2.66/1.33  ----------------------
% 2.66/1.34  Preprocessing        : 0.31
% 2.66/1.34  Parsing              : 0.17
% 2.66/1.34  CNF conversion       : 0.02
% 2.66/1.34  Main loop            : 0.25
% 2.66/1.34  Inferencing          : 0.10
% 2.66/1.34  Reduction            : 0.07
% 2.66/1.34  Demodulation         : 0.05
% 2.66/1.34  BG Simplification    : 0.02
% 2.66/1.34  Subsumption          : 0.05
% 2.66/1.34  Abstraction          : 0.01
% 2.66/1.34  MUC search           : 0.00
% 2.66/1.34  Cooper               : 0.00
% 2.66/1.34  Total                : 0.60
% 2.66/1.34  Index Insertion      : 0.00
% 2.66/1.34  Index Deletion       : 0.00
% 2.66/1.34  Index Matching       : 0.00
% 2.66/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
