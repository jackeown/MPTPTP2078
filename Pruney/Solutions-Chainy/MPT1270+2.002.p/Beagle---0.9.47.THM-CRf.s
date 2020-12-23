%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:55 EST 2020

% Result     : Theorem 6.76s
% Output     : CNFRefutation 6.76s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 107 expanded)
%              Number of leaves         :   34 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 167 expanded)
%              Number of equality atoms :   39 (  43 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_zfmisc_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_73,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_58,plain,
    ( ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_104,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3717,plain,(
    ! [B_199,A_200] :
      ( v2_tops_1(B_199,A_200)
      | k1_tops_1(A_200,B_199) != k1_xboole_0
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3728,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_3717])).

tff(c_3733,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3728])).

tff(c_3734,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_3733])).

tff(c_64,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_212,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_64])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_212,c_6])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_429,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_16])).

tff(c_3300,plain,(
    ! [A_189,B_190,C_191] :
      ( k7_subset_1(A_189,B_190,C_191) = k4_xboole_0(B_190,C_191)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(A_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3309,plain,(
    ! [C_191] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_191) = k4_xboole_0('#skF_2',C_191) ),
    inference(resolution,[status(thm)],[c_54,c_3300])).

tff(c_5565,plain,(
    ! [A_224,B_225] :
      ( k7_subset_1(u1_struct_0(A_224),B_225,k2_tops_1(A_224,B_225)) = k1_tops_1(A_224,B_225)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5573,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_5565])).

tff(c_5578,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_429,c_3309,c_5573])).

tff(c_5580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3734,c_5578])).

tff(c_5581,plain,(
    ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_10,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5582,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_9482,plain,(
    ! [A_372,B_373] :
      ( k1_tops_1(A_372,B_373) = k1_xboole_0
      | ~ v2_tops_1(B_373,A_372)
      | ~ m1_subset_1(B_373,k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ l1_pre_topc(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_9493,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_9482])).

tff(c_9498,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_5582,c_9493])).

tff(c_9330,plain,(
    ! [A_366,B_367,C_368] :
      ( k7_subset_1(A_366,B_367,C_368) = k4_xboole_0(B_367,C_368)
      | ~ m1_subset_1(B_367,k1_zfmisc_1(A_366)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9339,plain,(
    ! [C_368] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_368) = k4_xboole_0('#skF_2',C_368) ),
    inference(resolution,[status(thm)],[c_54,c_9330])).

tff(c_11242,plain,(
    ! [A_396,B_397] :
      ( k7_subset_1(u1_struct_0(A_396),B_397,k2_tops_1(A_396,B_397)) = k1_tops_1(A_396,B_397)
      | ~ m1_subset_1(B_397,k1_zfmisc_1(u1_struct_0(A_396)))
      | ~ l1_pre_topc(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11250,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_11242])).

tff(c_11255,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_9498,c_9339,c_11250])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_11262,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11255,c_18])).

tff(c_11266,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11262])).

tff(c_22,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5713,plain,(
    ! [A_238,B_239] : k1_setfam_1(k2_tarski(A_238,B_239)) = k3_xboole_0(A_238,B_239) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5728,plain,(
    ! [B_240,A_241] : k1_setfam_1(k2_tarski(B_240,A_241)) = k3_xboole_0(A_241,B_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5713])).

tff(c_32,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5751,plain,(
    ! [B_242,A_243] : k3_xboole_0(B_242,A_243) = k3_xboole_0(A_243,B_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_5728,c_32])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5786,plain,(
    ! [B_242,A_243] : r1_tarski(k3_xboole_0(B_242,A_243),A_243) ),
    inference(superposition,[status(thm),theory(equality)],[c_5751,c_8])).

tff(c_11370,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11266,c_5786])).

tff(c_11413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5581,c_11370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.76/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.44  
% 6.76/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.44  %$ v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_zfmisc_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.76/2.44  
% 6.76/2.44  %Foreground sorts:
% 6.76/2.44  
% 6.76/2.44  
% 6.76/2.44  %Background operators:
% 6.76/2.44  
% 6.76/2.44  
% 6.76/2.44  %Foreground operators:
% 6.76/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.76/2.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.76/2.44  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.76/2.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.76/2.44  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 6.76/2.44  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 6.76/2.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.76/2.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.76/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.76/2.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.76/2.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.76/2.44  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.76/2.44  tff('#skF_2', type, '#skF_2': $i).
% 6.76/2.44  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.76/2.44  tff('#skF_1', type, '#skF_1': $i).
% 6.76/2.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.76/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.76/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.76/2.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.76/2.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.76/2.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.76/2.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.76/2.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.76/2.44  
% 6.76/2.46  tff(f_125, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 6.76/2.46  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 6.76/2.46  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.76/2.46  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.76/2.46  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.76/2.46  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 6.76/2.46  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.76/2.46  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.76/2.46  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.76/2.46  tff(f_73, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.76/2.46  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.76/2.46  tff(c_58, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.76/2.46  tff(c_104, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 6.76/2.46  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.76/2.46  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.76/2.46  tff(c_3717, plain, (![B_199, A_200]: (v2_tops_1(B_199, A_200) | k1_tops_1(A_200, B_199)!=k1_xboole_0 | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.76/2.46  tff(c_3728, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_3717])).
% 6.76/2.46  tff(c_3733, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3728])).
% 6.76/2.46  tff(c_3734, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_104, c_3733])).
% 6.76/2.46  tff(c_64, plain, (v2_tops_1('#skF_2', '#skF_1') | r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.76/2.46  tff(c_212, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_104, c_64])).
% 6.76/2.46  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.76/2.46  tff(c_216, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_212, c_6])).
% 6.76/2.46  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.76/2.46  tff(c_429, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_216, c_16])).
% 6.76/2.46  tff(c_3300, plain, (![A_189, B_190, C_191]: (k7_subset_1(A_189, B_190, C_191)=k4_xboole_0(B_190, C_191) | ~m1_subset_1(B_190, k1_zfmisc_1(A_189)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.76/2.46  tff(c_3309, plain, (![C_191]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_191)=k4_xboole_0('#skF_2', C_191))), inference(resolution, [status(thm)], [c_54, c_3300])).
% 6.76/2.46  tff(c_5565, plain, (![A_224, B_225]: (k7_subset_1(u1_struct_0(A_224), B_225, k2_tops_1(A_224, B_225))=k1_tops_1(A_224, B_225) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.76/2.46  tff(c_5573, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_5565])).
% 6.76/2.46  tff(c_5578, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_429, c_3309, c_5573])).
% 6.76/2.46  tff(c_5580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3734, c_5578])).
% 6.76/2.46  tff(c_5581, plain, (~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_58])).
% 6.76/2.46  tff(c_10, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.76/2.46  tff(c_5582, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 6.76/2.46  tff(c_9482, plain, (![A_372, B_373]: (k1_tops_1(A_372, B_373)=k1_xboole_0 | ~v2_tops_1(B_373, A_372) | ~m1_subset_1(B_373, k1_zfmisc_1(u1_struct_0(A_372))) | ~l1_pre_topc(A_372))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.76/2.46  tff(c_9493, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_9482])).
% 6.76/2.46  tff(c_9498, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_5582, c_9493])).
% 6.76/2.46  tff(c_9330, plain, (![A_366, B_367, C_368]: (k7_subset_1(A_366, B_367, C_368)=k4_xboole_0(B_367, C_368) | ~m1_subset_1(B_367, k1_zfmisc_1(A_366)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.76/2.46  tff(c_9339, plain, (![C_368]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_368)=k4_xboole_0('#skF_2', C_368))), inference(resolution, [status(thm)], [c_54, c_9330])).
% 6.76/2.46  tff(c_11242, plain, (![A_396, B_397]: (k7_subset_1(u1_struct_0(A_396), B_397, k2_tops_1(A_396, B_397))=k1_tops_1(A_396, B_397) | ~m1_subset_1(B_397, k1_zfmisc_1(u1_struct_0(A_396))) | ~l1_pre_topc(A_396))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.76/2.46  tff(c_11250, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_11242])).
% 6.76/2.46  tff(c_11255, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_9498, c_9339, c_11250])).
% 6.76/2.46  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.76/2.46  tff(c_11262, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11255, c_18])).
% 6.76/2.46  tff(c_11266, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_11262])).
% 6.76/2.46  tff(c_22, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.76/2.46  tff(c_5713, plain, (![A_238, B_239]: (k1_setfam_1(k2_tarski(A_238, B_239))=k3_xboole_0(A_238, B_239))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.76/2.46  tff(c_5728, plain, (![B_240, A_241]: (k1_setfam_1(k2_tarski(B_240, A_241))=k3_xboole_0(A_241, B_240))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5713])).
% 6.76/2.46  tff(c_32, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.76/2.46  tff(c_5751, plain, (![B_242, A_243]: (k3_xboole_0(B_242, A_243)=k3_xboole_0(A_243, B_242))), inference(superposition, [status(thm), theory('equality')], [c_5728, c_32])).
% 6.76/2.46  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.76/2.46  tff(c_5786, plain, (![B_242, A_243]: (r1_tarski(k3_xboole_0(B_242, A_243), A_243))), inference(superposition, [status(thm), theory('equality')], [c_5751, c_8])).
% 6.76/2.46  tff(c_11370, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11266, c_5786])).
% 6.76/2.46  tff(c_11413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5581, c_11370])).
% 6.76/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.46  
% 6.76/2.46  Inference rules
% 6.76/2.46  ----------------------
% 6.76/2.46  #Ref     : 0
% 6.76/2.46  #Sup     : 2768
% 6.76/2.46  #Fact    : 0
% 6.76/2.46  #Define  : 0
% 6.76/2.46  #Split   : 3
% 6.76/2.46  #Chain   : 0
% 6.76/2.46  #Close   : 0
% 6.76/2.46  
% 6.76/2.46  Ordering : KBO
% 6.76/2.46  
% 6.76/2.46  Simplification rules
% 6.76/2.46  ----------------------
% 6.76/2.46  #Subsume      : 67
% 6.76/2.46  #Demod        : 2557
% 6.76/2.46  #Tautology    : 2177
% 6.76/2.46  #SimpNegUnit  : 6
% 6.76/2.46  #BackRed      : 0
% 6.76/2.46  
% 6.76/2.46  #Partial instantiations: 0
% 6.76/2.46  #Strategies tried      : 1
% 6.76/2.46  
% 6.76/2.46  Timing (in seconds)
% 6.76/2.46  ----------------------
% 6.76/2.46  Preprocessing        : 0.34
% 6.76/2.46  Parsing              : 0.19
% 6.76/2.46  CNF conversion       : 0.02
% 6.76/2.46  Main loop            : 1.35
% 6.76/2.46  Inferencing          : 0.40
% 6.76/2.46  Reduction            : 0.62
% 6.76/2.46  Demodulation         : 0.51
% 6.76/2.46  BG Simplification    : 0.04
% 6.76/2.46  Subsumption          : 0.20
% 6.76/2.46  Abstraction          : 0.06
% 6.76/2.46  MUC search           : 0.00
% 6.76/2.46  Cooper               : 0.00
% 6.76/2.46  Total                : 1.72
% 6.76/2.46  Index Insertion      : 0.00
% 6.76/2.46  Index Deletion       : 0.00
% 6.76/2.46  Index Matching       : 0.00
% 6.76/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
