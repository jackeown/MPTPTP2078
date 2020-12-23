%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:00 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   60 (  99 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 221 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_95,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(B_47,k2_tops_1(A_48,B_47))
      | ~ v2_tops_1(B_47,A_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_99,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_103,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_99])).

tff(c_104,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_45,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(B_32,k2_pre_topc(A_33,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_47,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_50,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_47])).

tff(c_26,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_80,plain,(
    ! [A_43,B_44] :
      ( v2_tops_1(k2_pre_topc(A_43,B_44),A_43)
      | ~ v3_tops_1(B_44,A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_84,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_80])).

tff(c_88,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_84])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k2_pre_topc(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_153,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k2_pre_topc(A_65,B_66),k2_tops_1(A_65,k2_pre_topc(A_65,B_66)))
      | ~ v2_tops_1(k2_pre_topc(A_65,B_66),A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [A_27,C_3,B_28] :
      ( r1_tarski(A_27,C_3)
      | ~ r1_tarski(B_28,C_3)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2])).

tff(c_204,plain,(
    ! [A_81,A_82,B_83] :
      ( r1_tarski(A_81,k2_tops_1(A_82,k2_pre_topc(A_82,B_83)))
      | ~ r1_tarski(A_81,k2_pre_topc(A_82,B_83))
      | ~ v2_tops_1(k2_pre_topc(A_82,B_83),A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_153,c_38])).

tff(c_106,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k2_tops_1(A_51,k2_pre_topc(A_51,B_52)),k2_tops_1(A_51,B_52))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_112,plain,(
    ! [A_27,A_51,B_52] :
      ( r1_tarski(A_27,k2_tops_1(A_51,B_52))
      | ~ r1_tarski(A_27,k2_tops_1(A_51,k2_pre_topc(A_51,B_52)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_106,c_38])).

tff(c_312,plain,(
    ! [A_93,A_94,B_95] :
      ( r1_tarski(A_93,k2_tops_1(A_94,B_95))
      | ~ r1_tarski(A_93,k2_pre_topc(A_94,B_95))
      | ~ v2_tops_1(k2_pre_topc(A_94,B_95),A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_204,c_112])).

tff(c_316,plain,(
    ! [A_93] :
      ( r1_tarski(A_93,k2_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_93,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_88,c_312])).

tff(c_370,plain,(
    ! [A_96] :
      ( r1_tarski(A_96,k2_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_96,k2_pre_topc('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_316])).

tff(c_20,plain,(
    ! [B_22,A_20] :
      ( v2_tops_1(B_22,A_20)
      | ~ r1_tarski(B_22,k2_tops_1(A_20,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_375,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_370,c_20])).

tff(c_387,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30,c_28,c_375])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_387])).

tff(c_391,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_452,plain,(
    ! [A_106,B_107] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_106),B_107),A_106)
      | ~ v2_tops_1(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_458,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_452,c_24])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_391,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:37:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.32  
% 2.24/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.32  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.24/1.32  
% 2.24/1.32  %Foreground sorts:
% 2.24/1.32  
% 2.24/1.32  
% 2.24/1.32  %Background operators:
% 2.24/1.32  
% 2.24/1.32  
% 2.24/1.32  %Foreground operators:
% 2.24/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.32  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.24/1.32  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.24/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.32  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.24/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.24/1.32  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.24/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.32  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.24/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.32  
% 2.71/1.34  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 2.71/1.34  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 2.71/1.34  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.71/1.34  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 2.71/1.34  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.71/1.34  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.71/1.34  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.71/1.34  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 2.71/1.34  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 2.71/1.34  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.34  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.34  tff(c_95, plain, (![B_47, A_48]: (r1_tarski(B_47, k2_tops_1(A_48, B_47)) | ~v2_tops_1(B_47, A_48) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.34  tff(c_99, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_95])).
% 2.71/1.34  tff(c_103, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_99])).
% 2.71/1.34  tff(c_104, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_103])).
% 2.71/1.34  tff(c_45, plain, (![B_32, A_33]: (r1_tarski(B_32, k2_pre_topc(A_33, B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.34  tff(c_47, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_45])).
% 2.71/1.34  tff(c_50, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_47])).
% 2.71/1.34  tff(c_26, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.34  tff(c_80, plain, (![A_43, B_44]: (v2_tops_1(k2_pre_topc(A_43, B_44), A_43) | ~v3_tops_1(B_44, A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.71/1.34  tff(c_84, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_80])).
% 2.71/1.34  tff(c_88, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_84])).
% 2.71/1.34  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k2_pre_topc(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.71/1.34  tff(c_153, plain, (![A_65, B_66]: (r1_tarski(k2_pre_topc(A_65, B_66), k2_tops_1(A_65, k2_pre_topc(A_65, B_66))) | ~v2_tops_1(k2_pre_topc(A_65, B_66), A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_6, c_95])).
% 2.71/1.34  tff(c_32, plain, (![A_27, B_28]: (k2_xboole_0(A_27, k4_xboole_0(B_28, A_27))=B_28 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.71/1.34  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.71/1.34  tff(c_38, plain, (![A_27, C_3, B_28]: (r1_tarski(A_27, C_3) | ~r1_tarski(B_28, C_3) | ~r1_tarski(A_27, B_28))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2])).
% 2.71/1.34  tff(c_204, plain, (![A_81, A_82, B_83]: (r1_tarski(A_81, k2_tops_1(A_82, k2_pre_topc(A_82, B_83))) | ~r1_tarski(A_81, k2_pre_topc(A_82, B_83)) | ~v2_tops_1(k2_pre_topc(A_82, B_83), A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_153, c_38])).
% 2.71/1.34  tff(c_106, plain, (![A_51, B_52]: (r1_tarski(k2_tops_1(A_51, k2_pre_topc(A_51, B_52)), k2_tops_1(A_51, B_52)) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.71/1.34  tff(c_112, plain, (![A_27, A_51, B_52]: (r1_tarski(A_27, k2_tops_1(A_51, B_52)) | ~r1_tarski(A_27, k2_tops_1(A_51, k2_pre_topc(A_51, B_52))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_106, c_38])).
% 2.71/1.34  tff(c_312, plain, (![A_93, A_94, B_95]: (r1_tarski(A_93, k2_tops_1(A_94, B_95)) | ~r1_tarski(A_93, k2_pre_topc(A_94, B_95)) | ~v2_tops_1(k2_pre_topc(A_94, B_95), A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_204, c_112])).
% 2.71/1.34  tff(c_316, plain, (![A_93]: (r1_tarski(A_93, k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_93, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_88, c_312])).
% 2.71/1.34  tff(c_370, plain, (![A_96]: (r1_tarski(A_96, k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(A_96, k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_316])).
% 2.71/1.34  tff(c_20, plain, (![B_22, A_20]: (v2_tops_1(B_22, A_20) | ~r1_tarski(B_22, k2_tops_1(A_20, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.34  tff(c_375, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_370, c_20])).
% 2.71/1.34  tff(c_387, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_30, c_28, c_375])).
% 2.71/1.34  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_387])).
% 2.71/1.34  tff(c_391, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_103])).
% 2.71/1.34  tff(c_452, plain, (![A_106, B_107]: (v1_tops_1(k3_subset_1(u1_struct_0(A_106), B_107), A_106) | ~v2_tops_1(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.71/1.34  tff(c_24, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.34  tff(c_458, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_452, c_24])).
% 2.71/1.34  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_391, c_458])).
% 2.71/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.34  
% 2.71/1.34  Inference rules
% 2.71/1.34  ----------------------
% 2.71/1.34  #Ref     : 0
% 2.71/1.34  #Sup     : 101
% 2.71/1.34  #Fact    : 0
% 2.71/1.34  #Define  : 0
% 2.71/1.34  #Split   : 3
% 2.71/1.34  #Chain   : 0
% 2.71/1.34  #Close   : 0
% 2.71/1.34  
% 2.71/1.34  Ordering : KBO
% 2.71/1.34  
% 2.71/1.34  Simplification rules
% 2.71/1.34  ----------------------
% 2.71/1.34  #Subsume      : 9
% 2.71/1.34  #Demod        : 54
% 2.71/1.34  #Tautology    : 17
% 2.71/1.34  #SimpNegUnit  : 1
% 2.71/1.34  #BackRed      : 0
% 2.71/1.34  
% 2.71/1.34  #Partial instantiations: 0
% 2.71/1.34  #Strategies tried      : 1
% 2.71/1.34  
% 2.71/1.34  Timing (in seconds)
% 2.71/1.34  ----------------------
% 2.71/1.34  Preprocessing        : 0.28
% 2.71/1.34  Parsing              : 0.15
% 2.71/1.34  CNF conversion       : 0.02
% 2.71/1.34  Main loop            : 0.31
% 2.71/1.34  Inferencing          : 0.12
% 2.71/1.34  Reduction            : 0.08
% 2.71/1.34  Demodulation         : 0.05
% 2.71/1.34  BG Simplification    : 0.02
% 2.71/1.34  Subsumption          : 0.07
% 2.71/1.34  Abstraction          : 0.01
% 2.71/1.34  MUC search           : 0.00
% 2.71/1.34  Cooper               : 0.00
% 2.71/1.34  Total                : 0.62
% 2.71/1.34  Index Insertion      : 0.00
% 2.71/1.34  Index Deletion       : 0.00
% 2.71/1.34  Index Matching       : 0.00
% 2.71/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
