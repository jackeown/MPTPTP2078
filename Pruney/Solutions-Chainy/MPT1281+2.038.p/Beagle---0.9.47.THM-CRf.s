%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:18 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 154 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :   97 ( 326 expanded)
%              Number of equality atoms :   22 (  49 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_101,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tops_1(A_43,B_44),B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_109,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_101])).

tff(c_114,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_109])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_242,plain,(
    ! [A_60,B_61] :
      ( k2_pre_topc(A_60,k1_tops_1(A_60,B_61)) = B_61
      | ~ v5_tops_1(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_252,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_242])).

tff(c_258,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_252])).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_259,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_24])).

tff(c_47,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k3_subset_1(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [B_9,A_8] :
      ( k4_xboole_0(B_9,A_8) = k3_subset_1(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_47])).

tff(c_121,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_114,c_58])).

tff(c_74,plain,(
    ! [A_36,B_37,C_38] :
      ( k7_subset_1(A_36,B_37,C_38) = k4_xboole_0(B_37,C_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [C_38] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_38) = k4_xboole_0('#skF_2',C_38) ),
    inference(resolution,[status(thm)],[c_28,c_74])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k1_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_339,plain,(
    ! [A_75,B_76] :
      ( k7_subset_1(u1_struct_0(A_75),k2_pre_topc(A_75,B_76),k1_tops_1(A_75,B_76)) = k2_tops_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_348,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_339])).

tff(c_355,plain,
    ( k4_xboole_0('#skF_2',k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_83,c_348])).

tff(c_487,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_490,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_487])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_490])).

tff(c_499,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k2_pre_topc(A_10,k2_pre_topc(A_10,B_11)) = k2_pre_topc(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_509,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_499,c_12])).

tff(c_534,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_258,c_258,c_509])).

tff(c_20,plain,(
    ! [A_17,B_19] :
      ( k7_subset_1(u1_struct_0(A_17),k2_pre_topc(A_17,B_19),k1_tops_1(A_17,B_19)) = k2_tops_1(A_17,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_548,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_20])).

tff(c_552,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_121,c_83,c_548])).

tff(c_41,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k3_subset_1(A_28,B_29),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k3_subset_1(A_28,B_29),A_28)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(resolution,[status(thm)],[c_41,c_8])).

tff(c_596,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_45])).

tff(c_607,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_596])).

tff(c_633,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_607])).

tff(c_637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:56:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.36  
% 2.76/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.37  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.76/1.37  
% 2.76/1.37  %Foreground sorts:
% 2.76/1.37  
% 2.76/1.37  
% 2.76/1.37  %Background operators:
% 2.76/1.37  
% 2.76/1.37  
% 2.76/1.37  %Foreground operators:
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.37  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.76/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.76/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.76/1.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.76/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.37  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.76/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.37  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.37  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.76/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.37  
% 2.76/1.38  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 2.76/1.38  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.76/1.38  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.76/1.38  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 2.76/1.38  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.76/1.38  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.76/1.38  tff(f_62, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.76/1.38  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.76/1.38  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 2.76/1.38  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.76/1.38  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.76/1.38  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.76/1.38  tff(c_101, plain, (![A_43, B_44]: (r1_tarski(k1_tops_1(A_43, B_44), B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.38  tff(c_109, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_101])).
% 2.76/1.38  tff(c_114, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_109])).
% 2.76/1.38  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.38  tff(c_26, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.76/1.38  tff(c_242, plain, (![A_60, B_61]: (k2_pre_topc(A_60, k1_tops_1(A_60, B_61))=B_61 | ~v5_tops_1(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.76/1.38  tff(c_252, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_242])).
% 2.76/1.38  tff(c_258, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_252])).
% 2.76/1.38  tff(c_24, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.76/1.38  tff(c_259, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_24])).
% 2.76/1.38  tff(c_47, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k3_subset_1(A_32, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.38  tff(c_58, plain, (![B_9, A_8]: (k4_xboole_0(B_9, A_8)=k3_subset_1(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_10, c_47])).
% 2.76/1.38  tff(c_121, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_114, c_58])).
% 2.76/1.38  tff(c_74, plain, (![A_36, B_37, C_38]: (k7_subset_1(A_36, B_37, C_38)=k4_xboole_0(B_37, C_38) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.38  tff(c_83, plain, (![C_38]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_38)=k4_xboole_0('#skF_2', C_38))), inference(resolution, [status(thm)], [c_28, c_74])).
% 2.76/1.38  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k1_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.38  tff(c_339, plain, (![A_75, B_76]: (k7_subset_1(u1_struct_0(A_75), k2_pre_topc(A_75, B_76), k1_tops_1(A_75, B_76))=k2_tops_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.76/1.38  tff(c_348, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_258, c_339])).
% 2.76/1.38  tff(c_355, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_83, c_348])).
% 2.76/1.38  tff(c_487, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_355])).
% 2.76/1.38  tff(c_490, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_487])).
% 2.76/1.38  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_490])).
% 2.76/1.38  tff(c_499, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_355])).
% 2.76/1.38  tff(c_12, plain, (![A_10, B_11]: (k2_pre_topc(A_10, k2_pre_topc(A_10, B_11))=k2_pre_topc(A_10, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.38  tff(c_509, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_499, c_12])).
% 2.76/1.38  tff(c_534, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_258, c_258, c_509])).
% 2.76/1.38  tff(c_20, plain, (![A_17, B_19]: (k7_subset_1(u1_struct_0(A_17), k2_pre_topc(A_17, B_19), k1_tops_1(A_17, B_19))=k2_tops_1(A_17, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.76/1.38  tff(c_548, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_534, c_20])).
% 2.76/1.38  tff(c_552, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_121, c_83, c_548])).
% 2.76/1.38  tff(c_41, plain, (![A_28, B_29]: (m1_subset_1(k3_subset_1(A_28, B_29), k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.38  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.38  tff(c_45, plain, (![A_28, B_29]: (r1_tarski(k3_subset_1(A_28, B_29), A_28) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(resolution, [status(thm)], [c_41, c_8])).
% 2.76/1.38  tff(c_596, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_552, c_45])).
% 2.76/1.38  tff(c_607, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_259, c_596])).
% 2.76/1.38  tff(c_633, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_10, c_607])).
% 2.76/1.38  tff(c_637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_633])).
% 2.76/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.38  
% 2.76/1.38  Inference rules
% 2.76/1.38  ----------------------
% 2.76/1.38  #Ref     : 0
% 2.76/1.38  #Sup     : 145
% 2.76/1.38  #Fact    : 0
% 2.76/1.38  #Define  : 0
% 2.76/1.38  #Split   : 1
% 2.76/1.38  #Chain   : 0
% 2.76/1.38  #Close   : 0
% 2.76/1.38  
% 2.76/1.38  Ordering : KBO
% 2.76/1.38  
% 2.76/1.38  Simplification rules
% 2.76/1.38  ----------------------
% 2.76/1.38  #Subsume      : 2
% 2.76/1.38  #Demod        : 69
% 2.76/1.38  #Tautology    : 57
% 2.76/1.38  #SimpNegUnit  : 1
% 2.76/1.38  #BackRed      : 2
% 2.76/1.38  
% 2.76/1.38  #Partial instantiations: 0
% 2.76/1.38  #Strategies tried      : 1
% 2.76/1.38  
% 2.76/1.38  Timing (in seconds)
% 2.76/1.38  ----------------------
% 2.76/1.38  Preprocessing        : 0.31
% 2.76/1.38  Parsing              : 0.17
% 2.76/1.38  CNF conversion       : 0.02
% 2.76/1.38  Main loop            : 0.31
% 2.76/1.38  Inferencing          : 0.12
% 2.76/1.38  Reduction            : 0.09
% 2.76/1.38  Demodulation         : 0.06
% 2.76/1.39  BG Simplification    : 0.02
% 2.76/1.39  Subsumption          : 0.06
% 2.76/1.39  Abstraction          : 0.02
% 2.76/1.39  MUC search           : 0.00
% 2.76/1.39  Cooper               : 0.00
% 2.76/1.39  Total                : 0.65
% 2.76/1.39  Index Insertion      : 0.00
% 2.76/1.39  Index Deletion       : 0.00
% 2.76/1.39  Index Matching       : 0.00
% 2.76/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
