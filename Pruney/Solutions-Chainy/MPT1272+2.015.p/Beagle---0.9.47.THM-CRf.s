%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:00 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 229 expanded)
%              Number of leaves         :   25 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 542 expanded)
%              Number of equality atoms :    7 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v1_tops_1(B,A)
                  & r1_tarski(B,C) )
               => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

tff(c_22,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_29,plain,(
    ! [A_27,B_28] :
      ( k3_subset_1(A_27,k3_subset_1(A_27,B_28)) = B_28
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_119,plain,(
    ! [B_41,A_42] :
      ( v2_tops_1(B_41,A_42)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_42),B_41),A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_126,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_119])).

tff(c_128,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_126])).

tff(c_150,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_154,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_154])).

tff(c_160,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k2_pre_topc(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_101,plain,(
    ! [A_39,B_40] :
      ( v2_tops_1(k2_pre_topc(A_39,B_40),A_39)
      | ~ v3_tops_1(B_40,A_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_108,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_101])).

tff(c_113,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_108])).

tff(c_176,plain,(
    ! [A_47,B_48] :
      ( k3_subset_1(u1_struct_0(A_47),k2_pre_topc(A_47,k3_subset_1(u1_struct_0(A_47),B_48))) = k1_tops_1(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_207,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_176])).

tff(c_211,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_160,c_207])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_10),B_12),A_10)
      | ~ v2_tops_1(B_12,A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_218,plain,
    ( v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_12])).

tff(c_233,plain,
    ( v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_113,c_218])).

tff(c_242,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_245,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_242])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_245])).

tff(c_250,plain,(
    v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_251,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_227,plain,
    ( m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_2])).

tff(c_309,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_227])).

tff(c_18,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k1_tops_1(A_16,B_18),B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_164,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_160,c_18])).

tff(c_172,plain,(
    r1_tarski(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_164])).

tff(c_266,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_tops_1(C_49,A_50)
      | ~ r1_tarski(B_51,C_49)
      | ~ v1_tops_1(B_51,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_626,plain,(
    ! [A_63] :
      ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_63)
      | ~ v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),A_63)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_172,c_266])).

tff(c_629,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_309,c_626])).

tff(c_632,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_160,c_250,c_629])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.39  
% 2.75/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.39  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.75/1.39  
% 2.75/1.39  %Foreground sorts:
% 2.75/1.39  
% 2.75/1.39  
% 2.75/1.39  %Background operators:
% 2.75/1.39  
% 2.75/1.39  
% 2.75/1.39  %Foreground operators:
% 2.75/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.39  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.75/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.39  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.75/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.75/1.39  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.75/1.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.75/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.39  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.75/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.39  
% 2.75/1.40  tff(f_95, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 2.75/1.40  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.75/1.40  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.75/1.40  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 2.75/1.40  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.75/1.40  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 2.75/1.40  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.75/1.40  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.75/1.40  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_1)).
% 2.75/1.40  tff(c_22, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.75/1.40  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.75/1.40  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.75/1.40  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.40  tff(c_29, plain, (![A_27, B_28]: (k3_subset_1(A_27, k3_subset_1(A_27, B_28))=B_28 | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.40  tff(c_32, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_29])).
% 2.75/1.40  tff(c_119, plain, (![B_41, A_42]: (v2_tops_1(B_41, A_42) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_42), B_41), A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.75/1.40  tff(c_126, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_119])).
% 2.75/1.40  tff(c_128, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_126])).
% 2.75/1.40  tff(c_150, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_128])).
% 2.75/1.40  tff(c_154, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_150])).
% 2.75/1.40  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_154])).
% 2.75/1.40  tff(c_160, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_128])).
% 2.75/1.40  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k2_pre_topc(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.40  tff(c_24, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.75/1.40  tff(c_101, plain, (![A_39, B_40]: (v2_tops_1(k2_pre_topc(A_39, B_40), A_39) | ~v3_tops_1(B_40, A_39) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.40  tff(c_108, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_101])).
% 2.75/1.40  tff(c_113, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_108])).
% 2.75/1.40  tff(c_176, plain, (![A_47, B_48]: (k3_subset_1(u1_struct_0(A_47), k2_pre_topc(A_47, k3_subset_1(u1_struct_0(A_47), B_48)))=k1_tops_1(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.75/1.40  tff(c_207, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_176])).
% 2.75/1.40  tff(c_211, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_160, c_207])).
% 2.75/1.40  tff(c_12, plain, (![A_10, B_12]: (v1_tops_1(k3_subset_1(u1_struct_0(A_10), B_12), A_10) | ~v2_tops_1(B_12, A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.75/1.40  tff(c_218, plain, (v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_211, c_12])).
% 2.75/1.40  tff(c_233, plain, (v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_113, c_218])).
% 2.75/1.40  tff(c_242, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_233])).
% 2.75/1.40  tff(c_245, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_242])).
% 2.75/1.40  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_245])).
% 2.75/1.40  tff(c_250, plain, (v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1')), inference(splitRight, [status(thm)], [c_233])).
% 2.75/1.40  tff(c_251, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_233])).
% 2.75/1.40  tff(c_227, plain, (m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_211, c_2])).
% 2.75/1.40  tff(c_309, plain, (m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_227])).
% 2.75/1.40  tff(c_18, plain, (![A_16, B_18]: (r1_tarski(k1_tops_1(A_16, B_18), B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.75/1.40  tff(c_164, plain, (r1_tarski(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_160, c_18])).
% 2.75/1.40  tff(c_172, plain, (r1_tarski(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_164])).
% 2.75/1.40  tff(c_266, plain, (![C_49, A_50, B_51]: (v1_tops_1(C_49, A_50) | ~r1_tarski(B_51, C_49) | ~v1_tops_1(B_51, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.75/1.40  tff(c_626, plain, (![A_63]: (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_63) | ~v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), A_63) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_172, c_266])).
% 2.75/1.40  tff(c_629, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_309, c_626])).
% 2.75/1.40  tff(c_632, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_160, c_250, c_629])).
% 2.75/1.40  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_632])).
% 2.75/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.40  
% 2.75/1.40  Inference rules
% 2.75/1.40  ----------------------
% 2.75/1.40  #Ref     : 0
% 2.75/1.40  #Sup     : 138
% 2.75/1.40  #Fact    : 0
% 2.75/1.40  #Define  : 0
% 2.75/1.40  #Split   : 9
% 2.75/1.40  #Chain   : 0
% 2.75/1.40  #Close   : 0
% 2.75/1.40  
% 2.75/1.40  Ordering : KBO
% 2.75/1.40  
% 2.75/1.40  Simplification rules
% 2.75/1.40  ----------------------
% 2.75/1.40  #Subsume      : 4
% 2.75/1.40  #Demod        : 133
% 2.75/1.40  #Tautology    : 48
% 2.75/1.40  #SimpNegUnit  : 2
% 2.75/1.40  #BackRed      : 0
% 2.75/1.40  
% 2.75/1.40  #Partial instantiations: 0
% 2.75/1.40  #Strategies tried      : 1
% 2.75/1.40  
% 2.75/1.40  Timing (in seconds)
% 2.75/1.40  ----------------------
% 2.75/1.41  Preprocessing        : 0.29
% 2.75/1.41  Parsing              : 0.16
% 2.75/1.41  CNF conversion       : 0.02
% 2.75/1.41  Main loop            : 0.36
% 2.75/1.41  Inferencing          : 0.13
% 2.75/1.41  Reduction            : 0.12
% 2.75/1.41  Demodulation         : 0.08
% 2.75/1.41  BG Simplification    : 0.02
% 2.75/1.41  Subsumption          : 0.07
% 2.75/1.41  Abstraction          : 0.02
% 2.75/1.41  MUC search           : 0.00
% 2.75/1.41  Cooper               : 0.00
% 2.75/1.41  Total                : 0.68
% 2.75/1.41  Index Insertion      : 0.00
% 2.75/1.41  Index Deletion       : 0.00
% 2.75/1.41  Index Matching       : 0.00
% 2.75/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
