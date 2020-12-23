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
% DateTime   : Thu Dec  3 10:21:59 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 182 expanded)
%              Number of leaves         :   28 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 456 expanded)
%              Number of equality atoms :   19 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_303,plain,(
    ! [B_57,A_58] :
      ( v2_tops_1(B_57,A_58)
      | k1_tops_1(A_58,B_57) != k1_xboole_0
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_309,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_303])).

tff(c_313,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_309])).

tff(c_314,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_176,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(B_45,k2_pre_topc(A_46,B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_178,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_176])).

tff(c_181,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_178])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_328,plain,(
    ! [A_63,B_64] :
      ( v2_tops_1(k2_pre_topc(A_63,B_64),A_63)
      | ~ v3_tops_1(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_332,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_328])).

tff(c_336,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_332])).

tff(c_315,plain,(
    ! [A_59,B_60] :
      ( k1_tops_1(A_59,B_60) = k1_xboole_0
      | ~ v2_tops_1(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_413,plain,(
    ! [A_78,B_79] :
      ( k1_tops_1(A_78,k2_pre_topc(A_78,B_79)) = k1_xboole_0
      | ~ v2_tops_1(k2_pre_topc(A_78,B_79),A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_14,c_315])).

tff(c_415,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_336,c_413])).

tff(c_418,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_415])).

tff(c_26,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_tarski(k1_tops_1(A_18,B_22),k1_tops_1(A_18,C_24))
      | ~ r1_tarski(B_22,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_425,plain,(
    ! [B_22] :
      ( r1_tarski(k1_tops_1('#skF_1',B_22),k1_xboole_0)
      | ~ r1_tarski(B_22,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_26])).

tff(c_431,plain,(
    ! [B_22] :
      ( r1_tarski(k1_tops_1('#skF_1',B_22),k1_xboole_0)
      | ~ r1_tarski(B_22,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_425])).

tff(c_501,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_511,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_501])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_511])).

tff(c_517,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [B_34] : k4_xboole_0(B_34,B_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_12,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [B_34] : r1_tarski(k1_xboole_0,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_12])).

tff(c_392,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(k1_tops_1(A_73,B_74),k1_tops_1(A_73,C_75))
      | ~ r1_tarski(B_74,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_602,plain,(
    ! [A_90,C_91,B_92] :
      ( k1_tops_1(A_90,C_91) = k1_tops_1(A_90,B_92)
      | ~ r1_tarski(k1_tops_1(A_90,C_91),k1_tops_1(A_90,B_92))
      | ~ r1_tarski(B_92,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_392,c_2])).

tff(c_605,plain,(
    ! [B_92] :
      ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',B_92)
      | ~ r1_tarski(k1_xboole_0,k1_tops_1('#skF_1',B_92))
      | ~ r1_tarski(B_92,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_602])).

tff(c_629,plain,(
    ! [B_93] :
      ( k1_tops_1('#skF_1',B_93) = k1_xboole_0
      | ~ r1_tarski(B_93,k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_517,c_56,c_418,c_605])).

tff(c_639,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_629])).

tff(c_648,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_639])).

tff(c_650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_648])).

tff(c_651,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_684,plain,(
    ! [A_102,B_103] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_102),B_103),A_102)
      | ~ v2_tops_1(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_690,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_684,c_32])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_651,c_690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:39:32 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.36  
% 2.53/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.36  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.53/1.36  
% 2.53/1.36  %Foreground sorts:
% 2.53/1.36  
% 2.53/1.36  
% 2.53/1.36  %Background operators:
% 2.53/1.36  
% 2.53/1.36  
% 2.53/1.36  %Foreground operators:
% 2.53/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.36  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.53/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.36  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.53/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.53/1.36  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.53/1.36  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.53/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.36  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.53/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.36  
% 2.85/1.38  tff(f_99, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 2.85/1.38  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 2.85/1.38  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.85/1.38  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.85/1.38  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 2.85/1.38  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 2.85/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.85/1.38  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.85/1.38  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.85/1.38  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 2.85/1.38  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.85/1.38  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.85/1.38  tff(c_303, plain, (![B_57, A_58]: (v2_tops_1(B_57, A_58) | k1_tops_1(A_58, B_57)!=k1_xboole_0 | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.85/1.38  tff(c_309, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_303])).
% 2.85/1.38  tff(c_313, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_309])).
% 2.85/1.38  tff(c_314, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_313])).
% 2.85/1.38  tff(c_176, plain, (![B_45, A_46]: (r1_tarski(B_45, k2_pre_topc(A_46, B_45)) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.85/1.38  tff(c_178, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_176])).
% 2.85/1.38  tff(c_181, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_178])).
% 2.85/1.38  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.85/1.38  tff(c_34, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.85/1.38  tff(c_328, plain, (![A_63, B_64]: (v2_tops_1(k2_pre_topc(A_63, B_64), A_63) | ~v3_tops_1(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.85/1.38  tff(c_332, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_328])).
% 2.85/1.38  tff(c_336, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_332])).
% 2.85/1.38  tff(c_315, plain, (![A_59, B_60]: (k1_tops_1(A_59, B_60)=k1_xboole_0 | ~v2_tops_1(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.85/1.38  tff(c_413, plain, (![A_78, B_79]: (k1_tops_1(A_78, k2_pre_topc(A_78, B_79))=k1_xboole_0 | ~v2_tops_1(k2_pre_topc(A_78, B_79), A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_14, c_315])).
% 2.85/1.38  tff(c_415, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0 | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_336, c_413])).
% 2.85/1.38  tff(c_418, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_415])).
% 2.85/1.38  tff(c_26, plain, (![A_18, B_22, C_24]: (r1_tarski(k1_tops_1(A_18, B_22), k1_tops_1(A_18, C_24)) | ~r1_tarski(B_22, C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.85/1.38  tff(c_425, plain, (![B_22]: (r1_tarski(k1_tops_1('#skF_1', B_22), k1_xboole_0) | ~r1_tarski(B_22, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_418, c_26])).
% 2.85/1.38  tff(c_431, plain, (![B_22]: (r1_tarski(k1_tops_1('#skF_1', B_22), k1_xboole_0) | ~r1_tarski(B_22, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_425])).
% 2.85/1.38  tff(c_501, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_431])).
% 2.85/1.38  tff(c_511, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_501])).
% 2.85/1.38  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_511])).
% 2.85/1.38  tff(c_517, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_431])).
% 2.85/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.38  tff(c_42, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.38  tff(c_51, plain, (![B_34]: (k4_xboole_0(B_34, B_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_42])).
% 2.85/1.38  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.38  tff(c_56, plain, (![B_34]: (r1_tarski(k1_xboole_0, B_34))), inference(superposition, [status(thm), theory('equality')], [c_51, c_12])).
% 2.85/1.38  tff(c_392, plain, (![A_73, B_74, C_75]: (r1_tarski(k1_tops_1(A_73, B_74), k1_tops_1(A_73, C_75)) | ~r1_tarski(B_74, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.85/1.38  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.38  tff(c_602, plain, (![A_90, C_91, B_92]: (k1_tops_1(A_90, C_91)=k1_tops_1(A_90, B_92) | ~r1_tarski(k1_tops_1(A_90, C_91), k1_tops_1(A_90, B_92)) | ~r1_tarski(B_92, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_392, c_2])).
% 2.85/1.38  tff(c_605, plain, (![B_92]: (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', B_92) | ~r1_tarski(k1_xboole_0, k1_tops_1('#skF_1', B_92)) | ~r1_tarski(B_92, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_418, c_602])).
% 2.85/1.38  tff(c_629, plain, (![B_93]: (k1_tops_1('#skF_1', B_93)=k1_xboole_0 | ~r1_tarski(B_93, k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_517, c_56, c_418, c_605])).
% 2.85/1.38  tff(c_639, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_629])).
% 2.85/1.38  tff(c_648, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_181, c_639])).
% 2.85/1.38  tff(c_650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_648])).
% 2.85/1.38  tff(c_651, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_313])).
% 2.85/1.38  tff(c_684, plain, (![A_102, B_103]: (v1_tops_1(k3_subset_1(u1_struct_0(A_102), B_103), A_102) | ~v2_tops_1(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.38  tff(c_32, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.85/1.38  tff(c_690, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_684, c_32])).
% 2.85/1.38  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_651, c_690])).
% 2.85/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.38  
% 2.85/1.38  Inference rules
% 2.85/1.38  ----------------------
% 2.85/1.38  #Ref     : 0
% 2.85/1.38  #Sup     : 142
% 2.85/1.38  #Fact    : 0
% 2.85/1.38  #Define  : 0
% 2.85/1.38  #Split   : 4
% 2.85/1.38  #Chain   : 0
% 2.85/1.38  #Close   : 0
% 2.85/1.38  
% 2.85/1.38  Ordering : KBO
% 2.85/1.38  
% 2.85/1.38  Simplification rules
% 2.85/1.38  ----------------------
% 2.85/1.38  #Subsume      : 19
% 2.85/1.38  #Demod        : 101
% 2.85/1.38  #Tautology    : 65
% 2.85/1.38  #SimpNegUnit  : 3
% 2.85/1.38  #BackRed      : 0
% 2.85/1.38  
% 2.85/1.38  #Partial instantiations: 0
% 2.85/1.38  #Strategies tried      : 1
% 2.85/1.38  
% 2.85/1.38  Timing (in seconds)
% 2.85/1.38  ----------------------
% 2.85/1.38  Preprocessing        : 0.30
% 2.85/1.38  Parsing              : 0.17
% 2.85/1.38  CNF conversion       : 0.02
% 2.85/1.38  Main loop            : 0.33
% 2.85/1.38  Inferencing          : 0.12
% 2.85/1.38  Reduction            : 0.10
% 2.85/1.38  Demodulation         : 0.07
% 2.85/1.38  BG Simplification    : 0.02
% 2.85/1.38  Subsumption          : 0.07
% 2.85/1.38  Abstraction          : 0.01
% 2.85/1.38  MUC search           : 0.00
% 2.85/1.38  Cooper               : 0.00
% 2.85/1.39  Total                : 0.67
% 2.85/1.39  Index Insertion      : 0.00
% 2.85/1.39  Index Deletion       : 0.00
% 2.85/1.39  Index Matching       : 0.00
% 2.85/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
