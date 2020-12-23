%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:19 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 163 expanded)
%              Number of leaves         :   27 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  106 ( 374 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_702,plain,(
    ! [A_190,B_191] :
      ( k2_pre_topc(A_190,k1_tops_1(A_190,B_191)) = B_191
      | ~ v5_tops_1(B_191,A_190)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_708,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_702])).

tff(c_713,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_708])).

tff(c_22,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_714,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_22])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k1_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_22,B_24] :
      ( r1_tarski(k2_tops_1(A_22,k2_pre_topc(A_22,B_24)),k2_tops_1(A_22,B_24))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_718,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_20])).

tff(c_724,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_718])).

tff(c_757,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_724])).

tff(c_760,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_757])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_760])).

tff(c_766,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_724])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k2_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_245,plain,(
    ! [A_94,B_95,C_96] :
      ( k4_subset_1(A_94,B_95,C_96) = k2_xboole_0(B_95,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2282,plain,(
    ! [A_381,B_382,B_383] :
      ( k4_subset_1(u1_struct_0(A_381),B_382,k2_tops_1(A_381,B_383)) = k2_xboole_0(B_382,k2_tops_1(A_381,B_383))
      | ~ m1_subset_1(B_382,k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ m1_subset_1(B_383,k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ l1_pre_topc(A_381) ) ),
    inference(resolution,[status(thm)],[c_16,c_245])).

tff(c_3393,plain,(
    ! [A_452,B_453,B_454] :
      ( k4_subset_1(u1_struct_0(A_452),k1_tops_1(A_452,B_453),k2_tops_1(A_452,B_454)) = k2_xboole_0(k1_tops_1(A_452,B_453),k2_tops_1(A_452,B_454))
      | ~ m1_subset_1(B_454,k1_zfmisc_1(u1_struct_0(A_452)))
      | ~ m1_subset_1(B_453,k1_zfmisc_1(u1_struct_0(A_452)))
      | ~ l1_pre_topc(A_452) ) ),
    inference(resolution,[status(thm)],[c_14,c_2282])).

tff(c_860,plain,(
    ! [A_203,B_204] :
      ( k4_subset_1(u1_struct_0(A_203),B_204,k2_tops_1(A_203,B_204)) = k2_pre_topc(A_203,B_204)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_862,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_766,c_860])).

tff(c_871,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_713,c_862])).

tff(c_3403,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2'
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3393,c_871])).

tff(c_3415,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_766,c_3403])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_513,plain,(
    ! [A_157,B_158] :
      ( r1_tarski(k2_tops_1(A_157,k2_pre_topc(A_157,B_158)),k2_tops_1(A_157,B_158))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1018,plain,(
    ! [A_232,A_233,B_234] :
      ( r1_tarski(A_232,k2_tops_1(A_233,B_234))
      | ~ r1_tarski(A_232,k2_tops_1(A_233,k2_pre_topc(A_233,B_234)))
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_513,c_2])).

tff(c_2862,plain,(
    ! [A_408,B_409,B_410] :
      ( r1_tarski(k4_xboole_0(k2_tops_1(A_408,k2_pre_topc(A_408,B_409)),B_410),k2_tops_1(A_408,B_409))
      | ~ m1_subset_1(B_409,k1_zfmisc_1(u1_struct_0(A_408)))
      | ~ l1_pre_topc(A_408) ) ),
    inference(resolution,[status(thm)],[c_4,c_1018])).

tff(c_2884,plain,(
    ! [B_410] :
      ( r1_tarski(k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),B_410),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_2862])).

tff(c_2896,plain,(
    ! [B_411] : r1_tarski(k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),B_411),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_766,c_2884])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k2_xboole_0(B_7,C_8))
      | ~ r1_tarski(k4_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2911,plain,(
    ! [B_411] : r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0(B_411,k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_2896,c_6])).

tff(c_3427,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3415,c_2911])).

tff(c_3542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_714,c_3427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.13  
% 5.92/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.13  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 5.92/2.13  
% 5.92/2.13  %Foreground sorts:
% 5.92/2.13  
% 5.92/2.13  
% 5.92/2.13  %Background operators:
% 5.92/2.13  
% 5.92/2.13  
% 5.92/2.13  %Foreground operators:
% 5.92/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.92/2.13  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.92/2.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.92/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.92/2.13  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.92/2.13  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.92/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.92/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.92/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.92/2.13  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 5.92/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.92/2.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.92/2.13  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.92/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.92/2.13  
% 5.92/2.15  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 5.92/2.15  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 5.92/2.15  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 5.92/2.15  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 5.92/2.15  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.92/2.15  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.92/2.15  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.92/2.15  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.92/2.15  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.92/2.15  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.92/2.15  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.92/2.15  tff(c_24, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.92/2.15  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.92/2.15  tff(c_702, plain, (![A_190, B_191]: (k2_pre_topc(A_190, k1_tops_1(A_190, B_191))=B_191 | ~v5_tops_1(B_191, A_190) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.92/2.15  tff(c_708, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_702])).
% 5.92/2.15  tff(c_713, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_708])).
% 5.92/2.15  tff(c_22, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.92/2.15  tff(c_714, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_713, c_22])).
% 5.92/2.15  tff(c_14, plain, (![A_15, B_16]: (m1_subset_1(k1_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.92/2.15  tff(c_20, plain, (![A_22, B_24]: (r1_tarski(k2_tops_1(A_22, k2_pre_topc(A_22, B_24)), k2_tops_1(A_22, B_24)) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.92/2.15  tff(c_718, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_713, c_20])).
% 5.92/2.15  tff(c_724, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_718])).
% 5.92/2.15  tff(c_757, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_724])).
% 5.92/2.15  tff(c_760, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_757])).
% 5.92/2.15  tff(c_764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_760])).
% 5.92/2.15  tff(c_766, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_724])).
% 5.92/2.15  tff(c_16, plain, (![A_17, B_18]: (m1_subset_1(k2_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.15  tff(c_245, plain, (![A_94, B_95, C_96]: (k4_subset_1(A_94, B_95, C_96)=k2_xboole_0(B_95, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.92/2.15  tff(c_2282, plain, (![A_381, B_382, B_383]: (k4_subset_1(u1_struct_0(A_381), B_382, k2_tops_1(A_381, B_383))=k2_xboole_0(B_382, k2_tops_1(A_381, B_383)) | ~m1_subset_1(B_382, k1_zfmisc_1(u1_struct_0(A_381))) | ~m1_subset_1(B_383, k1_zfmisc_1(u1_struct_0(A_381))) | ~l1_pre_topc(A_381))), inference(resolution, [status(thm)], [c_16, c_245])).
% 5.92/2.15  tff(c_3393, plain, (![A_452, B_453, B_454]: (k4_subset_1(u1_struct_0(A_452), k1_tops_1(A_452, B_453), k2_tops_1(A_452, B_454))=k2_xboole_0(k1_tops_1(A_452, B_453), k2_tops_1(A_452, B_454)) | ~m1_subset_1(B_454, k1_zfmisc_1(u1_struct_0(A_452))) | ~m1_subset_1(B_453, k1_zfmisc_1(u1_struct_0(A_452))) | ~l1_pre_topc(A_452))), inference(resolution, [status(thm)], [c_14, c_2282])).
% 5.92/2.15  tff(c_860, plain, (![A_203, B_204]: (k4_subset_1(u1_struct_0(A_203), B_204, k2_tops_1(A_203, B_204))=k2_pre_topc(A_203, B_204) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.92/2.15  tff(c_862, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_766, c_860])).
% 5.92/2.15  tff(c_871, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_713, c_862])).
% 5.92/2.15  tff(c_3403, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2' | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3393, c_871])).
% 5.92/2.15  tff(c_3415, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_766, c_3403])).
% 5.92/2.15  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.92/2.15  tff(c_513, plain, (![A_157, B_158]: (r1_tarski(k2_tops_1(A_157, k2_pre_topc(A_157, B_158)), k2_tops_1(A_157, B_158)) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.92/2.15  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.15  tff(c_1018, plain, (![A_232, A_233, B_234]: (r1_tarski(A_232, k2_tops_1(A_233, B_234)) | ~r1_tarski(A_232, k2_tops_1(A_233, k2_pre_topc(A_233, B_234))) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(resolution, [status(thm)], [c_513, c_2])).
% 5.92/2.15  tff(c_2862, plain, (![A_408, B_409, B_410]: (r1_tarski(k4_xboole_0(k2_tops_1(A_408, k2_pre_topc(A_408, B_409)), B_410), k2_tops_1(A_408, B_409)) | ~m1_subset_1(B_409, k1_zfmisc_1(u1_struct_0(A_408))) | ~l1_pre_topc(A_408))), inference(resolution, [status(thm)], [c_4, c_1018])).
% 5.92/2.15  tff(c_2884, plain, (![B_410]: (r1_tarski(k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), B_410), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_713, c_2862])).
% 5.92/2.15  tff(c_2896, plain, (![B_411]: (r1_tarski(k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), B_411), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_766, c_2884])).
% 5.92/2.15  tff(c_6, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k2_xboole_0(B_7, C_8)) | ~r1_tarski(k4_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.92/2.15  tff(c_2911, plain, (![B_411]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0(B_411, k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))))), inference(resolution, [status(thm)], [c_2896, c_6])).
% 5.92/2.15  tff(c_3427, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3415, c_2911])).
% 5.92/2.15  tff(c_3542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_714, c_3427])).
% 5.92/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.15  
% 5.92/2.15  Inference rules
% 5.92/2.15  ----------------------
% 5.92/2.15  #Ref     : 0
% 5.92/2.15  #Sup     : 912
% 5.92/2.15  #Fact    : 0
% 5.92/2.15  #Define  : 0
% 5.92/2.15  #Split   : 3
% 5.92/2.15  #Chain   : 0
% 5.92/2.15  #Close   : 0
% 5.92/2.15  
% 5.92/2.15  Ordering : KBO
% 5.92/2.15  
% 5.92/2.15  Simplification rules
% 5.92/2.15  ----------------------
% 5.92/2.15  #Subsume      : 20
% 5.92/2.15  #Demod        : 110
% 5.92/2.15  #Tautology    : 85
% 5.92/2.15  #SimpNegUnit  : 2
% 5.92/2.15  #BackRed      : 1
% 5.92/2.15  
% 5.92/2.15  #Partial instantiations: 0
% 5.92/2.15  #Strategies tried      : 1
% 5.92/2.15  
% 5.92/2.15  Timing (in seconds)
% 5.92/2.15  ----------------------
% 5.92/2.15  Preprocessing        : 0.31
% 5.92/2.15  Parsing              : 0.16
% 5.92/2.15  CNF conversion       : 0.02
% 5.92/2.15  Main loop            : 1.07
% 5.92/2.15  Inferencing          : 0.31
% 5.92/2.15  Reduction            : 0.34
% 5.92/2.15  Demodulation         : 0.27
% 5.92/2.15  BG Simplification    : 0.04
% 5.92/2.15  Subsumption          : 0.31
% 5.92/2.15  Abstraction          : 0.04
% 5.92/2.15  MUC search           : 0.00
% 5.92/2.15  Cooper               : 0.00
% 5.92/2.15  Total                : 1.41
% 5.92/2.15  Index Insertion      : 0.00
% 5.92/2.15  Index Deletion       : 0.00
% 5.92/2.15  Index Matching       : 0.00
% 5.92/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
