%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:01 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 237 expanded)
%              Number of leaves         :   25 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :  123 ( 564 expanded)
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
             => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

tff(c_22,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
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

tff(c_144,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_147,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_144])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_147])).

tff(c_153,plain,(
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

tff(c_189,plain,(
    ! [A_47,B_48] :
      ( k3_subset_1(u1_struct_0(A_47),k2_pre_topc(A_47,k3_subset_1(u1_struct_0(A_47),B_48))) = k1_tops_1(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_220,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_189])).

tff(c_224,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_153,c_220])).

tff(c_12,plain,(
    ! [A_10,B_12] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_10),B_12),A_10)
      | ~ v2_tops_1(B_12,A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_232,plain,
    ( v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_12])).

tff(c_247,plain,
    ( v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_113,c_232])).

tff(c_253,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_256,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_253])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_256])).

tff(c_261,plain,(
    v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_262,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_241,plain,
    ( m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_2])).

tff(c_320,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_241])).

tff(c_18,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k1_tops_1(A_16,B_18),B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_176,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_153,c_18])).

tff(c_184,plain,(
    r1_tarski(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_176])).

tff(c_277,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_tops_1(C_49,A_50)
      | ~ r1_tarski(B_51,C_49)
      | ~ v1_tops_1(B_51,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_851,plain,(
    ! [A_67] :
      ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_67)
      | ~ v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),A_67)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_184,c_277])).

tff(c_854,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_320,c_851])).

tff(c_857,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_153,c_261,c_854])).

tff(c_10,plain,(
    ! [B_12,A_10] :
      ( v2_tops_1(B_12,A_10)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_10),B_12),A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_860,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_857,c_10])).

tff(c_863,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_860])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:38:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.43  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.83/1.43  
% 2.83/1.43  %Foreground sorts:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Background operators:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Foreground operators:
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.43  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.83/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.83/1.43  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.83/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.83/1.43  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.83/1.43  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.83/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.43  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.83/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.43  
% 2.83/1.45  tff(f_95, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 2.83/1.45  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.83/1.45  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.83/1.45  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 2.83/1.45  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.83/1.45  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 2.83/1.45  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.83/1.45  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.83/1.45  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_1)).
% 2.83/1.45  tff(c_22, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.83/1.45  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.83/1.45  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.83/1.45  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.45  tff(c_29, plain, (![A_27, B_28]: (k3_subset_1(A_27, k3_subset_1(A_27, B_28))=B_28 | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.45  tff(c_32, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_29])).
% 2.83/1.45  tff(c_119, plain, (![B_41, A_42]: (v2_tops_1(B_41, A_42) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_42), B_41), A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.83/1.45  tff(c_126, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_119])).
% 2.83/1.45  tff(c_128, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_126])).
% 2.83/1.45  tff(c_144, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_128])).
% 2.83/1.45  tff(c_147, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_144])).
% 2.83/1.45  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_147])).
% 2.83/1.45  tff(c_153, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_128])).
% 2.83/1.45  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k2_pre_topc(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.83/1.45  tff(c_24, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.83/1.45  tff(c_101, plain, (![A_39, B_40]: (v2_tops_1(k2_pre_topc(A_39, B_40), A_39) | ~v3_tops_1(B_40, A_39) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.45  tff(c_108, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_101])).
% 2.83/1.45  tff(c_113, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_108])).
% 2.83/1.45  tff(c_189, plain, (![A_47, B_48]: (k3_subset_1(u1_struct_0(A_47), k2_pre_topc(A_47, k3_subset_1(u1_struct_0(A_47), B_48)))=k1_tops_1(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.83/1.45  tff(c_220, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_189])).
% 2.83/1.45  tff(c_224, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_153, c_220])).
% 2.83/1.45  tff(c_12, plain, (![A_10, B_12]: (v1_tops_1(k3_subset_1(u1_struct_0(A_10), B_12), A_10) | ~v2_tops_1(B_12, A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.83/1.45  tff(c_232, plain, (v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_224, c_12])).
% 2.83/1.45  tff(c_247, plain, (v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_113, c_232])).
% 2.83/1.45  tff(c_253, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_247])).
% 2.83/1.45  tff(c_256, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_253])).
% 2.83/1.45  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_256])).
% 2.83/1.45  tff(c_261, plain, (v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1')), inference(splitRight, [status(thm)], [c_247])).
% 2.83/1.45  tff(c_262, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_247])).
% 2.83/1.45  tff(c_241, plain, (m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_224, c_2])).
% 2.83/1.45  tff(c_320, plain, (m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_241])).
% 2.83/1.45  tff(c_18, plain, (![A_16, B_18]: (r1_tarski(k1_tops_1(A_16, B_18), B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.83/1.45  tff(c_176, plain, (r1_tarski(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_153, c_18])).
% 2.83/1.45  tff(c_184, plain, (r1_tarski(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_176])).
% 2.83/1.45  tff(c_277, plain, (![C_49, A_50, B_51]: (v1_tops_1(C_49, A_50) | ~r1_tarski(B_51, C_49) | ~v1_tops_1(B_51, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.83/1.45  tff(c_851, plain, (![A_67]: (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_67) | ~v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), A_67) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_184, c_277])).
% 2.83/1.45  tff(c_854, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_320, c_851])).
% 2.83/1.45  tff(c_857, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_153, c_261, c_854])).
% 2.83/1.45  tff(c_10, plain, (![B_12, A_10]: (v2_tops_1(B_12, A_10) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_10), B_12), A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.83/1.45  tff(c_860, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_857, c_10])).
% 2.83/1.45  tff(c_863, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_860])).
% 2.83/1.45  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_863])).
% 2.83/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.45  
% 2.83/1.45  Inference rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Ref     : 0
% 2.83/1.45  #Sup     : 186
% 2.83/1.45  #Fact    : 0
% 2.83/1.45  #Define  : 0
% 2.83/1.45  #Split   : 13
% 2.83/1.45  #Chain   : 0
% 2.83/1.45  #Close   : 0
% 2.83/1.45  
% 2.83/1.45  Ordering : KBO
% 2.83/1.45  
% 2.83/1.45  Simplification rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Subsume      : 5
% 2.83/1.45  #Demod        : 220
% 2.83/1.45  #Tautology    : 62
% 2.83/1.45  #SimpNegUnit  : 3
% 2.83/1.45  #BackRed      : 0
% 2.83/1.45  
% 2.83/1.45  #Partial instantiations: 0
% 2.83/1.45  #Strategies tried      : 1
% 2.83/1.45  
% 2.83/1.45  Timing (in seconds)
% 2.83/1.45  ----------------------
% 2.83/1.45  Preprocessing        : 0.28
% 2.83/1.45  Parsing              : 0.16
% 2.83/1.45  CNF conversion       : 0.02
% 2.83/1.45  Main loop            : 0.40
% 2.83/1.45  Inferencing          : 0.14
% 2.83/1.45  Reduction            : 0.14
% 2.83/1.45  Demodulation         : 0.10
% 2.83/1.45  BG Simplification    : 0.02
% 2.83/1.45  Subsumption          : 0.08
% 2.83/1.45  Abstraction          : 0.02
% 2.83/1.45  MUC search           : 0.00
% 2.83/1.45  Cooper               : 0.00
% 2.83/1.45  Total                : 0.71
% 2.83/1.45  Index Insertion      : 0.00
% 2.83/1.45  Index Deletion       : 0.00
% 2.83/1.45  Index Matching       : 0.00
% 2.83/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
