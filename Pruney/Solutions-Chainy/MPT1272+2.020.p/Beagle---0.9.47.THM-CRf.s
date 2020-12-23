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
% DateTime   : Thu Dec  3 10:22:00 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 189 expanded)
%              Number of leaves         :   26 (  77 expanded)
%              Depth                    :   22
%              Number of atoms          :  133 ( 415 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

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

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

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

tff(c_64,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(B_36,k2_tops_1(A_37,B_36))
      | ~ v2_tops_1(B_36,A_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_68,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_72,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_68])).

tff(c_73,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_18,plain,(
    ! [A_17,B_19] :
      ( r1_tarski(k2_tops_1(A_17,k2_pre_topc(A_17,B_19)),k2_tops_1(A_17,B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_55,plain,(
    ! [A_34,B_35] :
      ( v2_tops_1(k2_pre_topc(A_34,B_35),A_34)
      | ~ v3_tops_1(B_35,A_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_59,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_63,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_59])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k2_pre_topc(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_pre_topc(A_32,B_33),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [B_10,A_8] :
      ( r1_tarski(B_10,k2_pre_topc(A_8,B_10))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k2_pre_topc(A_32,B_33),k2_pre_topc(A_32,k2_pre_topc(A_32,B_33)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_51,c_8])).

tff(c_98,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k2_pre_topc(A_48,B_49),k2_pre_topc(A_48,k2_pre_topc(A_48,B_49)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_51,c_8])).

tff(c_33,plain,(
    ! [B_29,A_30] :
      ( r1_tarski(B_29,k2_pre_topc(A_30,B_29))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_35,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_33])).

tff(c_38,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_35])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    k2_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [C_3] :
      ( r1_tarski('#skF_2',C_3)
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_102,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_46])).

tff(c_108,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_102])).

tff(c_113,plain,(
    k2_xboole_0('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_121,plain,(
    ! [C_50] :
      ( r1_tarski('#skF_2',C_50)
      | ~ r1_tarski(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')),C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_2])).

tff(c_125,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_121])).

tff(c_128,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_125])).

tff(c_141,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_144,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_144])).

tff(c_150,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_22,plain,(
    ! [B_22,A_20] :
      ( r1_tarski(B_22,k2_tops_1(A_20,B_22))
      | ~ v2_tops_1(B_22,A_20)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_152,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_150,c_22])).

tff(c_159,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_63,c_152])).

tff(c_181,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_159,c_46])).

tff(c_186,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_208,plain,(
    ! [C_55] :
      ( r1_tarski('#skF_2',C_55)
      | ~ r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_2])).

tff(c_212,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_208])).

tff(c_215,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_212])).

tff(c_20,plain,(
    ! [B_22,A_20] :
      ( v2_tops_1(B_22,A_20)
      | ~ r1_tarski(B_22,k2_tops_1(A_20,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_217,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_215,c_20])).

tff(c_223,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_217])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_223])).

tff(c_227,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_253,plain,(
    ! [A_63,B_64] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_63),B_64),A_63)
      | ~ v2_tops_1(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_259,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_253,c_24])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_227,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n015.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 16:20:08 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.96/1.21  
% 1.96/1.21  %Foreground sorts:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Background operators:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Foreground operators:
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.21  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 1.96/1.21  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.96/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.96/1.21  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.96/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.96/1.21  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 1.96/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.96/1.21  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 1.96/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.21  
% 1.96/1.23  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 1.96/1.23  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 1.96/1.23  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 1.96/1.23  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 1.96/1.23  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 1.96/1.23  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 1.96/1.23  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.96/1.23  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.96/1.23  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 1.96/1.23  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.96/1.23  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.96/1.23  tff(c_64, plain, (![B_36, A_37]: (r1_tarski(B_36, k2_tops_1(A_37, B_36)) | ~v2_tops_1(B_36, A_37) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.96/1.23  tff(c_68, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_64])).
% 1.96/1.23  tff(c_72, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_68])).
% 1.96/1.23  tff(c_73, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_72])).
% 1.96/1.23  tff(c_18, plain, (![A_17, B_19]: (r1_tarski(k2_tops_1(A_17, k2_pre_topc(A_17, B_19)), k2_tops_1(A_17, B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.96/1.23  tff(c_26, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.96/1.23  tff(c_55, plain, (![A_34, B_35]: (v2_tops_1(k2_pre_topc(A_34, B_35), A_34) | ~v3_tops_1(B_35, A_34) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.23  tff(c_59, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_55])).
% 1.96/1.23  tff(c_63, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_59])).
% 1.96/1.23  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k2_pre_topc(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.23  tff(c_51, plain, (![A_32, B_33]: (m1_subset_1(k2_pre_topc(A_32, B_33), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.23  tff(c_8, plain, (![B_10, A_8]: (r1_tarski(B_10, k2_pre_topc(A_8, B_10)) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.23  tff(c_54, plain, (![A_32, B_33]: (r1_tarski(k2_pre_topc(A_32, B_33), k2_pre_topc(A_32, k2_pre_topc(A_32, B_33))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_51, c_8])).
% 1.96/1.23  tff(c_98, plain, (![A_48, B_49]: (r1_tarski(k2_pre_topc(A_48, B_49), k2_pre_topc(A_48, k2_pre_topc(A_48, B_49))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_51, c_8])).
% 1.96/1.23  tff(c_33, plain, (![B_29, A_30]: (r1_tarski(B_29, k2_pre_topc(A_30, B_29)) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.23  tff(c_35, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_33])).
% 1.96/1.23  tff(c_38, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_35])).
% 1.96/1.23  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.23  tff(c_42, plain, (k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_4])).
% 1.96/1.23  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.23  tff(c_46, plain, (![C_3]: (r1_tarski('#skF_2', C_3) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), C_3))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2])).
% 1.96/1.23  tff(c_102, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_98, c_46])).
% 1.96/1.23  tff(c_108, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_102])).
% 1.96/1.23  tff(c_113, plain, (k2_xboole_0('#skF_2', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_108, c_4])).
% 1.96/1.23  tff(c_121, plain, (![C_50]: (r1_tarski('#skF_2', C_50) | ~r1_tarski(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), C_50))), inference(superposition, [status(thm), theory('equality')], [c_113, c_2])).
% 1.96/1.23  tff(c_125, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_121])).
% 1.96/1.23  tff(c_128, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_125])).
% 1.96/1.23  tff(c_141, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_128])).
% 1.96/1.23  tff(c_144, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_141])).
% 1.96/1.23  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_144])).
% 1.96/1.23  tff(c_150, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_128])).
% 1.96/1.23  tff(c_22, plain, (![B_22, A_20]: (r1_tarski(B_22, k2_tops_1(A_20, B_22)) | ~v2_tops_1(B_22, A_20) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.96/1.23  tff(c_152, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_150, c_22])).
% 1.96/1.23  tff(c_159, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_63, c_152])).
% 1.96/1.23  tff(c_181, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_159, c_46])).
% 1.96/1.23  tff(c_186, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_181, c_4])).
% 1.96/1.23  tff(c_208, plain, (![C_55]: (r1_tarski('#skF_2', C_55) | ~r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), C_55))), inference(superposition, [status(thm), theory('equality')], [c_186, c_2])).
% 1.96/1.23  tff(c_212, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_208])).
% 1.96/1.23  tff(c_215, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_212])).
% 1.96/1.23  tff(c_20, plain, (![B_22, A_20]: (v2_tops_1(B_22, A_20) | ~r1_tarski(B_22, k2_tops_1(A_20, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.96/1.23  tff(c_217, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_215, c_20])).
% 1.96/1.23  tff(c_223, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_217])).
% 1.96/1.23  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_223])).
% 1.96/1.23  tff(c_227, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 1.96/1.23  tff(c_253, plain, (![A_63, B_64]: (v1_tops_1(k3_subset_1(u1_struct_0(A_63), B_64), A_63) | ~v2_tops_1(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.23  tff(c_24, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 1.96/1.23  tff(c_259, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_253, c_24])).
% 1.96/1.23  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_227, c_259])).
% 1.96/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  Inference rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Ref     : 0
% 1.96/1.23  #Sup     : 50
% 1.96/1.23  #Fact    : 0
% 1.96/1.23  #Define  : 0
% 1.96/1.23  #Split   : 3
% 1.96/1.23  #Chain   : 0
% 1.96/1.23  #Close   : 0
% 1.96/1.23  
% 1.96/1.23  Ordering : KBO
% 1.96/1.23  
% 1.96/1.23  Simplification rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Subsume      : 1
% 1.96/1.23  #Demod        : 35
% 1.96/1.23  #Tautology    : 18
% 1.96/1.23  #SimpNegUnit  : 1
% 1.96/1.23  #BackRed      : 0
% 1.96/1.23  
% 1.96/1.23  #Partial instantiations: 0
% 1.96/1.23  #Strategies tried      : 1
% 1.96/1.23  
% 1.96/1.23  Timing (in seconds)
% 1.96/1.23  ----------------------
% 1.96/1.23  Preprocessing        : 0.28
% 1.96/1.23  Parsing              : 0.16
% 1.96/1.23  CNF conversion       : 0.02
% 1.96/1.23  Main loop            : 0.22
% 1.96/1.23  Inferencing          : 0.09
% 1.96/1.23  Reduction            : 0.06
% 2.24/1.23  Demodulation         : 0.04
% 2.24/1.23  BG Simplification    : 0.01
% 2.24/1.23  Subsumption          : 0.04
% 2.24/1.23  Abstraction          : 0.01
% 2.24/1.23  MUC search           : 0.00
% 2.24/1.23  Cooper               : 0.00
% 2.24/1.23  Total                : 0.54
% 2.24/1.23  Index Insertion      : 0.00
% 2.24/1.23  Index Deletion       : 0.00
% 2.24/1.23  Index Matching       : 0.00
% 2.24/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
