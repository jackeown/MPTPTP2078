%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:41 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 172 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  107 ( 372 expanded)
%              Number of equality atoms :    8 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k4_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C)),k1_tops_1(A,k4_subset_1(u1_struct_0(A),B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_29,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_37,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_29])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_29])).

tff(c_8,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k2_xboole_0(A_8,C_10),B_9)
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_37,B_38,C_39] :
      ( r1_tarski(A_37,k2_xboole_0(B_38,C_39))
      | ~ r1_tarski(k4_xboole_0(A_37,B_38),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_18,plain,(
    ! [A_18,B_22,C_24] :
      ( r1_tarski(k1_tops_1(A_18,B_22),k1_tops_1(A_18,C_24))
      | ~ r1_tarski(B_22,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k1_tops_1(A_51,B_52),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k1_tops_1(A_51,B_52),u1_struct_0(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_72,c_12])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [A_63,B_64,C_65] :
      ( k4_subset_1(A_63,B_64,C_65) = k2_xboole_0(B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_334,plain,(
    ! [A_82,B_83,B_84] :
      ( k4_subset_1(u1_struct_0(A_82),B_83,k1_tops_1(A_82,B_84)) = k2_xboole_0(B_83,k1_tops_1(A_82,B_84))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_16,c_90])).

tff(c_875,plain,(
    ! [A_124,A_125,B_126] :
      ( k4_subset_1(u1_struct_0(A_124),A_125,k1_tops_1(A_124,B_126)) = k2_xboole_0(A_125,k1_tops_1(A_124,B_126))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124)
      | ~ r1_tarski(A_125,u1_struct_0(A_124)) ) ),
    inference(resolution,[status(thm)],[c_14,c_334])).

tff(c_882,plain,(
    ! [A_125] :
      ( k4_subset_1(u1_struct_0('#skF_1'),A_125,k1_tops_1('#skF_1','#skF_3')) = k2_xboole_0(A_125,k1_tops_1('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_125,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_22,c_875])).

tff(c_893,plain,(
    ! [A_127] :
      ( k4_subset_1(u1_struct_0('#skF_1'),A_127,k1_tops_1('#skF_1','#skF_3')) = k2_xboole_0(A_127,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_127,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_882])).

tff(c_103,plain,(
    ! [B_66] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_66,'#skF_3') = k2_xboole_0(B_66,'#skF_3')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_90])).

tff(c_123,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_103])).

tff(c_20,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_128,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_20])).

tff(c_913,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_128])).

tff(c_1018,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_913])).

tff(c_1021,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_1018])).

tff(c_1025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1021])).

tff(c_1026,plain,(
    ~ r1_tarski(k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3')),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_1054,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_8,c_1026])).

tff(c_1468,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1054])).

tff(c_1471,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1468])).

tff(c_1474,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_6,c_1471])).

tff(c_1478,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_1474])).

tff(c_1490,plain,
    ( ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_1478])).

tff(c_1494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_36,c_1490])).

tff(c_1495,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1',k2_xboole_0('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_1499,plain,
    ( ~ r1_tarski('#skF_3',k2_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1495])).

tff(c_1502,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_51,c_1499])).

tff(c_1506,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_1502])).

tff(c_1509,plain,
    ( ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_1506])).

tff(c_1513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_36,c_1509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:24:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.55  
% 3.50/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.56  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.50/1.56  
% 3.50/1.56  %Foreground sorts:
% 3.50/1.56  
% 3.50/1.56  
% 3.50/1.56  %Background operators:
% 3.50/1.56  
% 3.50/1.56  
% 3.50/1.56  %Foreground operators:
% 3.50/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.50/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.50/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.56  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.50/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.50/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.50/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.50/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.50/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.56  
% 3.57/1.57  tff(f_78, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k4_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C)), k1_tops_1(A, k4_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tops_1)).
% 3.57/1.57  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.57/1.57  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.57/1.57  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.57/1.57  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.57/1.57  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 3.57/1.57  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.57/1.57  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.57/1.57  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.57/1.57  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.57/1.57  tff(c_29, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.57/1.57  tff(c_37, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_29])).
% 3.57/1.57  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.57/1.57  tff(c_36, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_29])).
% 3.57/1.57  tff(c_8, plain, (![A_8, C_10, B_9]: (r1_tarski(k2_xboole_0(A_8, C_10), B_9) | ~r1_tarski(C_10, B_9) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.57/1.57  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.57/1.57  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.57/1.57  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.57/1.57  tff(c_43, plain, (![A_37, B_38, C_39]: (r1_tarski(A_37, k2_xboole_0(B_38, C_39)) | ~r1_tarski(k4_xboole_0(A_37, B_38), C_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.57  tff(c_51, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(resolution, [status(thm)], [c_2, c_43])).
% 3.57/1.57  tff(c_18, plain, (![A_18, B_22, C_24]: (r1_tarski(k1_tops_1(A_18, B_22), k1_tops_1(A_18, C_24)) | ~r1_tarski(B_22, C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.57/1.57  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.57/1.57  tff(c_72, plain, (![A_51, B_52]: (m1_subset_1(k1_tops_1(A_51, B_52), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.57/1.57  tff(c_12, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.57/1.57  tff(c_76, plain, (![A_51, B_52]: (r1_tarski(k1_tops_1(A_51, B_52), u1_struct_0(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_72, c_12])).
% 3.57/1.57  tff(c_16, plain, (![A_16, B_17]: (m1_subset_1(k1_tops_1(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.57/1.57  tff(c_90, plain, (![A_63, B_64, C_65]: (k4_subset_1(A_63, B_64, C_65)=k2_xboole_0(B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/1.57  tff(c_334, plain, (![A_82, B_83, B_84]: (k4_subset_1(u1_struct_0(A_82), B_83, k1_tops_1(A_82, B_84))=k2_xboole_0(B_83, k1_tops_1(A_82, B_84)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_16, c_90])).
% 3.57/1.57  tff(c_875, plain, (![A_124, A_125, B_126]: (k4_subset_1(u1_struct_0(A_124), A_125, k1_tops_1(A_124, B_126))=k2_xboole_0(A_125, k1_tops_1(A_124, B_126)) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124) | ~r1_tarski(A_125, u1_struct_0(A_124)))), inference(resolution, [status(thm)], [c_14, c_334])).
% 3.57/1.57  tff(c_882, plain, (![A_125]: (k4_subset_1(u1_struct_0('#skF_1'), A_125, k1_tops_1('#skF_1', '#skF_3'))=k2_xboole_0(A_125, k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_125, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_22, c_875])).
% 3.57/1.57  tff(c_893, plain, (![A_127]: (k4_subset_1(u1_struct_0('#skF_1'), A_127, k1_tops_1('#skF_1', '#skF_3'))=k2_xboole_0(A_127, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_127, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_882])).
% 3.57/1.57  tff(c_103, plain, (![B_66]: (k4_subset_1(u1_struct_0('#skF_1'), B_66, '#skF_3')=k2_xboole_0(B_66, '#skF_3') | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_90])).
% 3.57/1.57  tff(c_123, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_103])).
% 3.57/1.57  tff(c_20, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.57/1.57  tff(c_128, plain, (~r1_tarski(k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_20])).
% 3.57/1.57  tff(c_913, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_893, c_128])).
% 3.57/1.57  tff(c_1018, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_913])).
% 3.57/1.57  tff(c_1021, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_1018])).
% 3.57/1.57  tff(c_1025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1021])).
% 3.57/1.57  tff(c_1026, plain, (~r1_tarski(k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_913])).
% 3.57/1.57  tff(c_1054, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_8, c_1026])).
% 3.57/1.57  tff(c_1468, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1054])).
% 3.57/1.57  tff(c_1471, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1468])).
% 3.57/1.57  tff(c_1474, plain, (~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_6, c_1471])).
% 3.57/1.57  tff(c_1478, plain, (~r1_tarski(k2_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_1474])).
% 3.57/1.57  tff(c_1490, plain, (~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_1478])).
% 3.57/1.57  tff(c_1494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37, c_36, c_1490])).
% 3.57/1.57  tff(c_1495, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', k2_xboole_0('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_1054])).
% 3.57/1.57  tff(c_1499, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1495])).
% 3.57/1.57  tff(c_1502, plain, (~m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_51, c_1499])).
% 3.57/1.57  tff(c_1506, plain, (~r1_tarski(k2_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_1502])).
% 3.57/1.57  tff(c_1509, plain, (~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_1506])).
% 3.57/1.57  tff(c_1513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37, c_36, c_1509])).
% 3.57/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.57  
% 3.57/1.57  Inference rules
% 3.57/1.57  ----------------------
% 3.57/1.57  #Ref     : 0
% 3.57/1.57  #Sup     : 305
% 3.57/1.57  #Fact    : 0
% 3.57/1.57  #Define  : 0
% 3.57/1.57  #Split   : 2
% 3.57/1.57  #Chain   : 0
% 3.57/1.57  #Close   : 0
% 3.57/1.57  
% 3.57/1.57  Ordering : KBO
% 3.57/1.57  
% 3.57/1.57  Simplification rules
% 3.57/1.57  ----------------------
% 3.57/1.57  #Subsume      : 9
% 3.57/1.57  #Demod        : 142
% 3.57/1.57  #Tautology    : 191
% 3.57/1.57  #SimpNegUnit  : 0
% 3.57/1.57  #BackRed      : 1
% 3.57/1.57  
% 3.57/1.57  #Partial instantiations: 0
% 3.57/1.57  #Strategies tried      : 1
% 3.57/1.57  
% 3.57/1.57  Timing (in seconds)
% 3.57/1.57  ----------------------
% 3.57/1.57  Preprocessing        : 0.31
% 3.57/1.57  Parsing              : 0.17
% 3.57/1.57  CNF conversion       : 0.02
% 3.57/1.57  Main loop            : 0.51
% 3.57/1.57  Inferencing          : 0.20
% 3.57/1.57  Reduction            : 0.15
% 3.57/1.58  Demodulation         : 0.11
% 3.57/1.58  BG Simplification    : 0.02
% 3.57/1.58  Subsumption          : 0.09
% 3.57/1.58  Abstraction          : 0.03
% 3.57/1.58  MUC search           : 0.00
% 3.57/1.58  Cooper               : 0.00
% 3.57/1.58  Total                : 0.85
% 3.57/1.58  Index Insertion      : 0.00
% 3.57/1.58  Index Deletion       : 0.00
% 3.57/1.58  Index Matching       : 0.00
% 3.57/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
