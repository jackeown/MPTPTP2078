%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:59 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 170 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 389 expanded)
%              Number of equality atoms :   24 (  98 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k2_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k2_tops_1(A,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_tops_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(c_26,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) != k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k2_tops_1(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_324,plain,(
    ! [A_57,B_58] :
      ( k1_tops_1(A_57,k2_tops_1(A_57,k2_tops_1(A_57,B_58))) = k1_xboole_0
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_328,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_324])).

tff(c_332,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_328])).

tff(c_337,plain,(
    ! [A_59,B_60] :
      ( k7_subset_1(u1_struct_0(A_59),k2_pre_topc(A_59,B_60),k1_tops_1(A_59,B_60)) = k2_tops_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_346,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_337])).

tff(c_350,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_xboole_0) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_346])).

tff(c_381,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_384,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_381])).

tff(c_387,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_384])).

tff(c_390,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_387])).

tff(c_394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_390])).

tff(c_396,plain,(
    m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( k7_subset_1(A_9,B_10,C_11) = k4_xboole_0(B_10,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_426,plain,(
    ! [C_11] : k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_11) = k4_xboole_0(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),C_11) ),
    inference(resolution,[status(thm)],[c_396,c_12])).

tff(c_300,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k2_tops_1(A_51,B_52),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( v4_pre_topc(k2_tops_1(A_17,B_18),A_17)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_308,plain,(
    ! [A_51,B_52] :
      ( v4_pre_topc(k2_tops_1(A_51,k2_tops_1(A_51,B_52)),A_51)
      | ~ v2_pre_topc(A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_300,c_20])).

tff(c_16,plain,(
    ! [A_12,B_14] :
      ( k2_pre_topc(A_12,B_14) = B_14
      | ~ v4_pre_topc(B_14,A_12)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_408,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ v4_pre_topc(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_396,c_16])).

tff(c_425,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ v4_pre_topc(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_408])).

tff(c_493,plain,(
    ~ v4_pre_topc(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_425])).

tff(c_496,plain,
    ( ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_308,c_493])).

tff(c_500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_32,c_496])).

tff(c_501,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_22,plain,(
    ! [A_19,B_21] :
      ( k7_subset_1(u1_struct_0(A_19),k2_pre_topc(A_19,B_21),k1_tops_1(A_19,B_21)) = k2_tops_1(A_19,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_512,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_22])).

tff(c_516,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_396,c_8,c_332,c_426,c_512])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.33  
% 2.36/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.34  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.36/1.34  
% 2.36/1.34  %Foreground sorts:
% 2.36/1.34  
% 2.36/1.34  
% 2.36/1.34  %Background operators:
% 2.36/1.34  
% 2.36/1.34  
% 2.36/1.34  %Foreground operators:
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.34  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.36/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.36/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.36/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.34  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.36/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.36/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.36/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.34  
% 2.36/1.35  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k2_tops_1(A, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_tops_1)).
% 2.36/1.35  tff(f_62, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 2.36/1.35  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l80_tops_1)).
% 2.36/1.35  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.36/1.35  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.36/1.35  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.36/1.35  tff(f_70, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_tops_1)).
% 2.36/1.35  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.36/1.35  tff(c_26, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))!=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.35  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.35  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.35  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k2_tops_1(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.36/1.35  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.36/1.35  tff(c_324, plain, (![A_57, B_58]: (k1_tops_1(A_57, k2_tops_1(A_57, k2_tops_1(A_57, B_58)))=k1_xboole_0 | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.36/1.35  tff(c_328, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_324])).
% 2.36/1.35  tff(c_332, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_328])).
% 2.36/1.35  tff(c_337, plain, (![A_59, B_60]: (k7_subset_1(u1_struct_0(A_59), k2_pre_topc(A_59, B_60), k1_tops_1(A_59, B_60))=k2_tops_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.36/1.35  tff(c_346, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_332, c_337])).
% 2.36/1.35  tff(c_350, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_xboole_0)=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_346])).
% 2.36/1.35  tff(c_381, plain, (~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_350])).
% 2.36/1.35  tff(c_384, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_381])).
% 2.36/1.35  tff(c_387, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_384])).
% 2.36/1.35  tff(c_390, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_387])).
% 2.36/1.35  tff(c_394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_390])).
% 2.36/1.35  tff(c_396, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_350])).
% 2.36/1.35  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.35  tff(c_12, plain, (![A_9, B_10, C_11]: (k7_subset_1(A_9, B_10, C_11)=k4_xboole_0(B_10, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.35  tff(c_426, plain, (![C_11]: (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_11)=k4_xboole_0(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), C_11))), inference(resolution, [status(thm)], [c_396, c_12])).
% 2.36/1.35  tff(c_300, plain, (![A_51, B_52]: (m1_subset_1(k2_tops_1(A_51, B_52), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.36/1.35  tff(c_20, plain, (![A_17, B_18]: (v4_pre_topc(k2_tops_1(A_17, B_18), A_17) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.36/1.35  tff(c_308, plain, (![A_51, B_52]: (v4_pre_topc(k2_tops_1(A_51, k2_tops_1(A_51, B_52)), A_51) | ~v2_pre_topc(A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_300, c_20])).
% 2.36/1.35  tff(c_16, plain, (![A_12, B_14]: (k2_pre_topc(A_12, B_14)=B_14 | ~v4_pre_topc(B_14, A_12) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.35  tff(c_408, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~v4_pre_topc(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_396, c_16])).
% 2.36/1.35  tff(c_425, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~v4_pre_topc(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_408])).
% 2.36/1.35  tff(c_493, plain, (~v4_pre_topc(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(splitLeft, [status(thm)], [c_425])).
% 2.36/1.35  tff(c_496, plain, (~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_308, c_493])).
% 2.36/1.35  tff(c_500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_32, c_496])).
% 2.36/1.35  tff(c_501, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_425])).
% 2.36/1.35  tff(c_22, plain, (![A_19, B_21]: (k7_subset_1(u1_struct_0(A_19), k2_pre_topc(A_19, B_21), k1_tops_1(A_19, B_21))=k2_tops_1(A_19, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.36/1.35  tff(c_512, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_501, c_22])).
% 2.36/1.35  tff(c_516, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_396, c_8, c_332, c_426, c_512])).
% 2.36/1.35  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_516])).
% 2.36/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  Inference rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Ref     : 0
% 2.36/1.35  #Sup     : 111
% 2.36/1.35  #Fact    : 0
% 2.36/1.35  #Define  : 0
% 2.36/1.35  #Split   : 3
% 2.36/1.35  #Chain   : 0
% 2.36/1.35  #Close   : 0
% 2.36/1.35  
% 2.36/1.35  Ordering : KBO
% 2.36/1.35  
% 2.36/1.35  Simplification rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Subsume      : 1
% 2.36/1.35  #Demod        : 65
% 2.36/1.35  #Tautology    : 72
% 2.36/1.35  #SimpNegUnit  : 2
% 2.36/1.35  #BackRed      : 1
% 2.36/1.35  
% 2.36/1.35  #Partial instantiations: 0
% 2.36/1.35  #Strategies tried      : 1
% 2.36/1.35  
% 2.36/1.35  Timing (in seconds)
% 2.36/1.35  ----------------------
% 2.57/1.35  Preprocessing        : 0.31
% 2.57/1.35  Parsing              : 0.16
% 2.57/1.35  CNF conversion       : 0.02
% 2.57/1.35  Main loop            : 0.25
% 2.57/1.35  Inferencing          : 0.09
% 2.57/1.35  Reduction            : 0.08
% 2.57/1.35  Demodulation         : 0.06
% 2.57/1.35  BG Simplification    : 0.02
% 2.57/1.36  Subsumption          : 0.04
% 2.57/1.36  Abstraction          : 0.02
% 2.57/1.36  MUC search           : 0.00
% 2.57/1.36  Cooper               : 0.00
% 2.57/1.36  Total                : 0.59
% 2.57/1.36  Index Insertion      : 0.00
% 2.57/1.36  Index Deletion       : 0.00
% 2.57/1.36  Index Matching       : 0.00
% 2.57/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
