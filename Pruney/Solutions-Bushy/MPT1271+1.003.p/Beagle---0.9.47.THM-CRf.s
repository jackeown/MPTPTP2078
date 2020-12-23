%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1271+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:41 EST 2020

% Result     : Theorem 48.91s
% Output     : CNFRefutation 49.06s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 299 expanded)
%              Number of leaves         :   26 ( 121 expanded)
%              Depth                    :    8
%              Number of atoms          :  186 ( 986 expanded)
%              Number of equality atoms :   16 (  83 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v3_tops_1(B,A)
                    & v3_tops_1(C,A) )
                 => v3_tops_1(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_tops_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => k2_pre_topc(A,k4_subset_1(u1_struct_0(A),B,C)) = k4_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_tops_1(B,A)
                  & v2_tops_1(C,A)
                  & v4_pre_topc(C,A) )
               => v2_tops_1(k4_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tops_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_77,plain,(
    ! [A_46,B_47,C_48] :
      ( k4_subset_1(A_46,B_47,C_48) = k2_xboole_0(B_47,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8532,plain,(
    ! [B_149] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_149,'#skF_3') = k2_xboole_0(B_149,'#skF_3')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_77])).

tff(c_8563,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_8532])).

tff(c_95,plain,(
    ! [B_49] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_49,'#skF_2') = k2_xboole_0(B_49,'#skF_2')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_115,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_95])).

tff(c_177,plain,(
    ! [A_50,C_51,B_52] :
      ( k4_subset_1(A_50,C_51,B_52) = k4_subset_1(A_50,B_52,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8657,plain,(
    ! [B_153] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_153,'#skF_3') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_177])).

tff(c_8683,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k4_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_8657])).

tff(c_8697,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8563,c_115,c_8683])).

tff(c_20,plain,(
    ~ v3_tops_1(k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8565,plain,(
    ~ v3_tops_1(k2_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8563,c_20])).

tff(c_8702,plain,(
    ~ v3_tops_1(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8697,c_8565])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_2') = k2_xboole_0('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_8604,plain,(
    ! [A_150,B_151,C_152] :
      ( k4_subset_1(u1_struct_0(A_150),k2_pre_topc(A_150,B_151),k2_pre_topc(A_150,C_152)) = k2_pre_topc(A_150,k4_subset_1(u1_struct_0(A_150),B_151,C_152))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k4_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95742,plain,(
    ! [A_569,B_570,C_571] :
      ( m1_subset_1(k2_pre_topc(A_569,k4_subset_1(u1_struct_0(A_569),B_570,C_571)),k1_zfmisc_1(u1_struct_0(A_569)))
      | ~ m1_subset_1(k2_pre_topc(A_569,C_571),k1_zfmisc_1(u1_struct_0(A_569)))
      | ~ m1_subset_1(k2_pre_topc(A_569,B_570),k1_zfmisc_1(u1_struct_0(A_569)))
      | ~ m1_subset_1(C_571,k1_zfmisc_1(u1_struct_0(A_569)))
      | ~ m1_subset_1(B_570,k1_zfmisc_1(u1_struct_0(A_569)))
      | ~ l1_pre_topc(A_569)
      | ~ v2_pre_topc(A_569) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8604,c_10])).

tff(c_95801,plain,
    ( m1_subset_1(k2_pre_topc('#skF_1',k2_xboole_0('#skF_2','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_95742])).

tff(c_95837,plain,
    ( m1_subset_1(k2_pre_topc('#skF_1',k2_xboole_0('#skF_2','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_28,c_95801])).

tff(c_98549,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_95837])).

tff(c_98552,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_98549])).

tff(c_98556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_98552])).

tff(c_98558,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_95837])).

tff(c_8564,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_xboole_0('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_8532])).

tff(c_95792,plain,
    ( m1_subset_1(k2_pre_topc('#skF_1',k2_xboole_0('#skF_3','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8564,c_95742])).

tff(c_95833,plain,
    ( m1_subset_1(k2_pre_topc('#skF_1',k2_xboole_0('#skF_3','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_26,c_95792])).

tff(c_98835,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_95833])).

tff(c_98892,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_98835])).

tff(c_98896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_98892])).

tff(c_98898,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_95833])).

tff(c_24,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_54,plain,(
    ! [A_44,B_45] :
      ( v2_tops_1(k2_pre_topc(A_44,B_45),A_44)
      | ~ v3_tops_1(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_54])).

tff(c_68,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_61])).

tff(c_22,plain,(
    v3_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_63,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ v3_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_54])).

tff(c_71,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22,c_63])).

tff(c_34,plain,(
    ! [A_37,B_38] :
      ( v4_pre_topc(k2_pre_topc(A_37,B_38),A_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_34])).

tff(c_47,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_40])).

tff(c_128,plain,
    ( m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_10])).

tff(c_132,plain,(
    m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_128])).

tff(c_8703,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8697,c_8563])).

tff(c_18,plain,(
    ! [A_24,B_28,C_30] :
      ( v2_tops_1(k4_subset_1(u1_struct_0(A_24),B_28,C_30),A_24)
      | ~ v4_pre_topc(C_30,A_24)
      | ~ v2_tops_1(C_30,A_24)
      | ~ v2_tops_1(B_28,A_24)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_95992,plain,(
    ! [A_572,B_573,C_574] :
      ( v2_tops_1(k2_pre_topc(A_572,k4_subset_1(u1_struct_0(A_572),B_573,C_574)),A_572)
      | ~ v4_pre_topc(k2_pre_topc(A_572,C_574),A_572)
      | ~ v2_tops_1(k2_pre_topc(A_572,C_574),A_572)
      | ~ v2_tops_1(k2_pre_topc(A_572,B_573),A_572)
      | ~ m1_subset_1(k2_pre_topc(A_572,C_574),k1_zfmisc_1(u1_struct_0(A_572)))
      | ~ m1_subset_1(k2_pre_topc(A_572,B_573),k1_zfmisc_1(u1_struct_0(A_572)))
      | ~ l1_pre_topc(A_572)
      | ~ v2_pre_topc(A_572)
      | ~ m1_subset_1(C_574,k1_zfmisc_1(u1_struct_0(A_572)))
      | ~ m1_subset_1(B_573,k1_zfmisc_1(u1_struct_0(A_572)))
      | ~ l1_pre_topc(A_572)
      | ~ v2_pre_topc(A_572) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8604,c_18])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( v3_tops_1(B_6,A_4)
      | ~ v2_tops_1(k2_pre_topc(A_4,B_6),A_4)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_129475,plain,(
    ! [A_676,B_677,C_678] :
      ( v3_tops_1(k4_subset_1(u1_struct_0(A_676),B_677,C_678),A_676)
      | ~ m1_subset_1(k4_subset_1(u1_struct_0(A_676),B_677,C_678),k1_zfmisc_1(u1_struct_0(A_676)))
      | ~ v4_pre_topc(k2_pre_topc(A_676,C_678),A_676)
      | ~ v2_tops_1(k2_pre_topc(A_676,C_678),A_676)
      | ~ v2_tops_1(k2_pre_topc(A_676,B_677),A_676)
      | ~ m1_subset_1(k2_pre_topc(A_676,C_678),k1_zfmisc_1(u1_struct_0(A_676)))
      | ~ m1_subset_1(k2_pre_topc(A_676,B_677),k1_zfmisc_1(u1_struct_0(A_676)))
      | ~ m1_subset_1(C_678,k1_zfmisc_1(u1_struct_0(A_676)))
      | ~ m1_subset_1(B_677,k1_zfmisc_1(u1_struct_0(A_676)))
      | ~ l1_pre_topc(A_676)
      | ~ v2_pre_topc(A_676) ) ),
    inference(resolution,[status(thm)],[c_95992,c_4])).

tff(c_129793,plain,
    ( v3_tops_1(k4_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k2_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_pre_topc(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8703,c_129475])).

tff(c_129997,plain,(
    v3_tops_1(k2_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_98558,c_98898,c_68,c_71,c_47,c_132,c_8703,c_129793])).

tff(c_129999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8702,c_129997])).

%------------------------------------------------------------------------------
