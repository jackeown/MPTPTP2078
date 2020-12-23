%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:13 EST 2020

% Result     : Theorem 11.17s
% Output     : CNFRefutation 11.17s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 163 expanded)
%              Number of leaves         :   30 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  103 ( 342 expanded)
%              Number of equality atoms :   25 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1416,plain,(
    ! [A_98,B_99] :
      ( k2_pre_topc(A_98,k1_tops_1(A_98,B_99)) = B_99
      | ~ v5_tops_1(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1422,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1416])).

tff(c_1427,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1422])).

tff(c_26,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1428,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_26])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k1_tops_1(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_25,B_27] :
      ( r1_tarski(k2_tops_1(A_25,k2_pre_topc(A_25,B_27)),k2_tops_1(A_25,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1432,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1427,c_24])).

tff(c_1438,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1432])).

tff(c_2078,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1438])).

tff(c_2081,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_2078])).

tff(c_2085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2081])).

tff(c_2087,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1438])).

tff(c_22,plain,(
    ! [A_22,B_24] :
      ( k4_subset_1(u1_struct_0(A_22),B_24,k2_tops_1(A_22,B_24)) = k2_pre_topc(A_22,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2089,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2087,c_22])).

tff(c_2105,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1427,c_2089])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_tops_1(A_20,B_21),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_291,plain,(
    ! [A_62,B_63,C_64] :
      ( k4_subset_1(A_62,B_63,C_64) = k2_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2558,plain,(
    ! [A_141,B_142,B_143] :
      ( k4_subset_1(u1_struct_0(A_141),B_142,k2_tops_1(A_141,B_143)) = k2_xboole_0(B_142,k2_tops_1(A_141,B_143))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(resolution,[status(thm)],[c_20,c_291])).

tff(c_2571,plain,(
    ! [A_18,B_19,B_143] :
      ( k4_subset_1(u1_struct_0(A_18),k1_tops_1(A_18,B_19),k2_tops_1(A_18,B_143)) = k2_xboole_0(k1_tops_1(A_18,B_19),k2_tops_1(A_18,B_143))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_18,c_2558])).

tff(c_13275,plain,
    ( k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2'
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2105,c_2571])).

tff(c_13288,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2087,c_13275])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [B_37,A_38] : k3_tarski(k2_tarski(B_37,A_38)) = k2_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_10])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [A_40,B_39] : r1_tarski(A_40,k2_xboole_0(B_39,A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_6])).

tff(c_13439,plain,(
    r1_tarski(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13288,c_125])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14293,plain,(
    k2_xboole_0(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_13439,c_4])).

tff(c_2086,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1438])).

tff(c_2117,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2086,c_4])).

tff(c_164,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(k2_xboole_0(A_43,B_45),C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_180,plain,(
    ! [A_43,B_45,B_7] : r1_tarski(A_43,k2_xboole_0(k2_xboole_0(A_43,B_45),B_7)) ),
    inference(resolution,[status(thm)],[c_6,c_164])).

tff(c_26830,plain,(
    ! [B_349] : r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),B_349)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2117,c_180])).

tff(c_26847,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14293,c_26830])).

tff(c_26905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1428,c_26847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.17/5.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.17/5.01  
% 11.17/5.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.17/5.01  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 11.17/5.01  
% 11.17/5.01  %Foreground sorts:
% 11.17/5.01  
% 11.17/5.01  
% 11.17/5.01  %Background operators:
% 11.17/5.01  
% 11.17/5.01  
% 11.17/5.01  %Foreground operators:
% 11.17/5.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.17/5.01  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.17/5.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.17/5.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.17/5.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.17/5.01  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.17/5.01  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.17/5.01  tff('#skF_2', type, '#skF_2': $i).
% 11.17/5.01  tff('#skF_1', type, '#skF_1': $i).
% 11.17/5.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.17/5.01  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 11.17/5.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.17/5.01  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.17/5.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.17/5.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.17/5.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.17/5.01  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.17/5.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.17/5.01  
% 11.17/5.02  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 11.17/5.02  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 11.17/5.02  tff(f_60, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 11.17/5.02  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 11.17/5.02  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 11.17/5.02  tff(f_66, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 11.17/5.02  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.17/5.02  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 11.17/5.02  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.17/5.02  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.17/5.02  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.17/5.02  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 11.17/5.02  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.17/5.02  tff(c_28, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.17/5.02  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.17/5.02  tff(c_1416, plain, (![A_98, B_99]: (k2_pre_topc(A_98, k1_tops_1(A_98, B_99))=B_99 | ~v5_tops_1(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.17/5.02  tff(c_1422, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1416])).
% 11.17/5.02  tff(c_1427, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_1422])).
% 11.17/5.02  tff(c_26, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.17/5.02  tff(c_1428, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1427, c_26])).
% 11.17/5.02  tff(c_18, plain, (![A_18, B_19]: (m1_subset_1(k1_tops_1(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.17/5.02  tff(c_24, plain, (![A_25, B_27]: (r1_tarski(k2_tops_1(A_25, k2_pre_topc(A_25, B_27)), k2_tops_1(A_25, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.17/5.02  tff(c_1432, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1427, c_24])).
% 11.17/5.02  tff(c_1438, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1432])).
% 11.17/5.02  tff(c_2078, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1438])).
% 11.17/5.02  tff(c_2081, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_2078])).
% 11.17/5.02  tff(c_2085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2081])).
% 11.17/5.02  tff(c_2087, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1438])).
% 11.17/5.02  tff(c_22, plain, (![A_22, B_24]: (k4_subset_1(u1_struct_0(A_22), B_24, k2_tops_1(A_22, B_24))=k2_pre_topc(A_22, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.17/5.02  tff(c_2089, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2087, c_22])).
% 11.17/5.02  tff(c_2105, plain, (k4_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1427, c_2089])).
% 11.17/5.02  tff(c_20, plain, (![A_20, B_21]: (m1_subset_1(k2_tops_1(A_20, B_21), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.17/5.02  tff(c_291, plain, (![A_62, B_63, C_64]: (k4_subset_1(A_62, B_63, C_64)=k2_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.17/5.02  tff(c_2558, plain, (![A_141, B_142, B_143]: (k4_subset_1(u1_struct_0(A_141), B_142, k2_tops_1(A_141, B_143))=k2_xboole_0(B_142, k2_tops_1(A_141, B_143)) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(resolution, [status(thm)], [c_20, c_291])).
% 11.17/5.02  tff(c_2571, plain, (![A_18, B_19, B_143]: (k4_subset_1(u1_struct_0(A_18), k1_tops_1(A_18, B_19), k2_tops_1(A_18, B_143))=k2_xboole_0(k1_tops_1(A_18, B_19), k2_tops_1(A_18, B_143)) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(resolution, [status(thm)], [c_18, c_2558])).
% 11.17/5.02  tff(c_13275, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2' | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2105, c_2571])).
% 11.17/5.02  tff(c_13288, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2087, c_13275])).
% 11.17/5.02  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.17/5.02  tff(c_67, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.17/5.02  tff(c_87, plain, (![B_37, A_38]: (k3_tarski(k2_tarski(B_37, A_38))=k2_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_8, c_67])).
% 11.17/5.02  tff(c_10, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.17/5.02  tff(c_110, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_87, c_10])).
% 11.17/5.02  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.17/5.02  tff(c_125, plain, (![A_40, B_39]: (r1_tarski(A_40, k2_xboole_0(B_39, A_40)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_6])).
% 11.17/5.02  tff(c_13439, plain, (r1_tarski(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13288, c_125])).
% 11.17/5.02  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.17/5.02  tff(c_14293, plain, (k2_xboole_0(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_13439, c_4])).
% 11.17/5.02  tff(c_2086, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_1438])).
% 11.17/5.02  tff(c_2117, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2086, c_4])).
% 11.17/5.02  tff(c_164, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(k2_xboole_0(A_43, B_45), C_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.17/5.02  tff(c_180, plain, (![A_43, B_45, B_7]: (r1_tarski(A_43, k2_xboole_0(k2_xboole_0(A_43, B_45), B_7)))), inference(resolution, [status(thm)], [c_6, c_164])).
% 11.17/5.02  tff(c_26830, plain, (![B_349]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), B_349)))), inference(superposition, [status(thm), theory('equality')], [c_2117, c_180])).
% 11.17/5.03  tff(c_26847, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14293, c_26830])).
% 11.17/5.03  tff(c_26905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1428, c_26847])).
% 11.17/5.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.17/5.03  
% 11.17/5.03  Inference rules
% 11.17/5.03  ----------------------
% 11.17/5.03  #Ref     : 0
% 11.17/5.03  #Sup     : 6489
% 11.17/5.03  #Fact    : 0
% 11.17/5.03  #Define  : 0
% 11.17/5.03  #Split   : 5
% 11.17/5.03  #Chain   : 0
% 11.17/5.03  #Close   : 0
% 11.17/5.03  
% 11.17/5.03  Ordering : KBO
% 11.17/5.03  
% 11.17/5.03  Simplification rules
% 11.17/5.03  ----------------------
% 11.17/5.03  #Subsume      : 755
% 11.17/5.03  #Demod        : 5655
% 11.17/5.03  #Tautology    : 3821
% 11.17/5.03  #SimpNegUnit  : 1
% 11.17/5.03  #BackRed      : 7
% 11.17/5.03  
% 11.17/5.03  #Partial instantiations: 0
% 11.17/5.03  #Strategies tried      : 1
% 11.17/5.03  
% 11.17/5.03  Timing (in seconds)
% 11.17/5.03  ----------------------
% 11.17/5.03  Preprocessing        : 0.33
% 11.17/5.03  Parsing              : 0.19
% 11.17/5.03  CNF conversion       : 0.02
% 11.17/5.03  Main loop            : 3.88
% 11.17/5.03  Inferencing          : 0.70
% 11.17/5.03  Reduction            : 2.33
% 11.17/5.03  Demodulation         : 2.11
% 11.17/5.03  BG Simplification    : 0.08
% 11.17/5.03  Subsumption          : 0.61
% 11.17/5.03  Abstraction          : 0.13
% 11.17/5.03  MUC search           : 0.00
% 11.17/5.03  Cooper               : 0.00
% 11.17/5.03  Total                : 4.25
% 11.17/5.03  Index Insertion      : 0.00
% 11.17/5.03  Index Deletion       : 0.00
% 11.17/5.03  Index Matching       : 0.00
% 11.17/5.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
