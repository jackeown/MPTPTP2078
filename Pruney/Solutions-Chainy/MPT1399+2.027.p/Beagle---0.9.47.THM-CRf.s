%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:22 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 498 expanded)
%              Number of leaves         :   35 ( 180 expanded)
%              Depth                    :   17
%              Number of atoms          :  146 (1597 expanded)
%              Number of equality atoms :   11 ( 215 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ~ ( m1_setfam_1(B,u1_struct_0(A))
              & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_30,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_24,plain,(
    ! [A_16] :
      ( v4_pre_topc(k2_struct_0(A_16),A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_89,plain,(
    ! [B_44,A_45] :
      ( m1_setfam_1(B_44,A_45)
      | ~ r1_tarski(A_45,k3_tarski(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [B_44] : m1_setfam_1(B_44,'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_89])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_71,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_77,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_81,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_84,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_34])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_17] :
      ( v3_pre_topc(k2_struct_0(A_17),A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6])).

tff(c_28,plain,(
    ! [A_18] :
      ( ~ m1_setfam_1(k1_xboole_0,u1_struct_0(A_18))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_49,plain,(
    ! [A_18] :
      ( ~ m1_setfam_1('#skF_3',u1_struct_0(A_18))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_28])).

tff(c_118,plain,(
    ! [A_51] :
      ( ~ m1_setfam_1('#skF_3',u1_struct_0(A_51))
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_49])).

tff(c_121,plain,
    ( ~ m1_setfam_1('#skF_3',k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_118])).

tff(c_122,plain,
    ( ~ m1_setfam_1('#skF_3',k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_121])).

tff(c_123,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_126,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_123])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_126])).

tff(c_132,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_146,plain,(
    ! [A_54] :
      ( m1_subset_1(k2_struct_0(A_54),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_149,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_146])).

tff(c_151,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_149])).

tff(c_46,plain,(
    ! [D_32] :
      ( v4_pre_topc(D_32,'#skF_1')
      | ~ r2_hidden(D_32,'#skF_3')
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_138,plain,(
    ! [D_32] :
      ( v4_pre_topc(D_32,'#skF_1')
      | ~ r2_hidden(D_32,'#skF_3')
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_46])).

tff(c_158,plain,
    ( v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_151,c_138])).

tff(c_199,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_42,plain,(
    ! [D_32] :
      ( r2_hidden(D_32,'#skF_3')
      | ~ r2_hidden('#skF_2',D_32)
      | ~ v4_pre_topc(D_32,'#skF_1')
      | ~ v3_pre_topc(D_32,'#skF_1')
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_187,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,'#skF_3')
      | ~ r2_hidden('#skF_2',D_63)
      | ~ v4_pre_topc(D_63,'#skF_1')
      | ~ v3_pre_topc(D_63,'#skF_1')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_42])).

tff(c_195,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_151,c_187])).

tff(c_329,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_195])).

tff(c_330,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_334,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_330])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_334])).

tff(c_339,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_341,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_344,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_341])).

tff(c_347,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_344])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2])).

tff(c_351,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_347,c_55])).

tff(c_131,plain,(
    ~ m1_setfam_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_360,plain,(
    ~ m1_setfam_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_131])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_360])).

tff(c_371,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_390,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_371])).

tff(c_394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_390])).

tff(c_396,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_407,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_396,c_16])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.31  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.31  
% 2.18/1.31  %Foreground sorts:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Background operators:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Foreground operators:
% 2.18/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.31  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.31  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.18/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.18/1.31  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.18/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.31  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.18/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.31  
% 2.63/1.33  tff(f_119, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.63/1.33  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.63/1.33  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.63/1.33  tff(f_37, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.63/1.33  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.63/1.33  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.63/1.33  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.63/1.33  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.63/1.33  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.63/1.33  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 2.63/1.33  tff(f_62, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.63/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.63/1.33  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.63/1.33  tff(c_30, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.33  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.33  tff(c_54, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4])).
% 2.63/1.33  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.33  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.33  tff(c_24, plain, (![A_16]: (v4_pre_topc(k2_struct_0(A_16), A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.63/1.33  tff(c_89, plain, (![B_44, A_45]: (m1_setfam_1(B_44, A_45) | ~r1_tarski(A_45, k3_tarski(B_44)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.63/1.33  tff(c_98, plain, (![B_44]: (m1_setfam_1(B_44, '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_89])).
% 2.63/1.33  tff(c_22, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.63/1.33  tff(c_71, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.63/1.33  tff(c_77, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_22, c_71])).
% 2.63/1.33  tff(c_81, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_77])).
% 2.63/1.33  tff(c_34, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.33  tff(c_84, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_34])).
% 2.63/1.33  tff(c_12, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.63/1.33  tff(c_26, plain, (![A_17]: (v3_pre_topc(k2_struct_0(A_17), A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.63/1.33  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.33  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.33  tff(c_50, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6])).
% 2.63/1.33  tff(c_28, plain, (![A_18]: (~m1_setfam_1(k1_xboole_0, u1_struct_0(A_18)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18)))) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.63/1.33  tff(c_49, plain, (![A_18]: (~m1_setfam_1('#skF_3', u1_struct_0(A_18)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18)))) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_28])).
% 2.63/1.33  tff(c_118, plain, (![A_51]: (~m1_setfam_1('#skF_3', u1_struct_0(A_51)) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_49])).
% 2.63/1.33  tff(c_121, plain, (~m1_setfam_1('#skF_3', k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_81, c_118])).
% 2.63/1.33  tff(c_122, plain, (~m1_setfam_1('#skF_3', k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_121])).
% 2.63/1.33  tff(c_123, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_122])).
% 2.63/1.33  tff(c_126, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_123])).
% 2.63/1.33  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_126])).
% 2.63/1.33  tff(c_132, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_122])).
% 2.63/1.33  tff(c_146, plain, (![A_54]: (m1_subset_1(k2_struct_0(A_54), k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.63/1.33  tff(c_149, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_81, c_146])).
% 2.63/1.33  tff(c_151, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_149])).
% 2.63/1.33  tff(c_46, plain, (![D_32]: (v4_pre_topc(D_32, '#skF_1') | ~r2_hidden(D_32, '#skF_3') | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.33  tff(c_138, plain, (![D_32]: (v4_pre_topc(D_32, '#skF_1') | ~r2_hidden(D_32, '#skF_3') | ~m1_subset_1(D_32, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_46])).
% 2.63/1.33  tff(c_158, plain, (v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_151, c_138])).
% 2.63/1.33  tff(c_199, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_158])).
% 2.63/1.33  tff(c_42, plain, (![D_32]: (r2_hidden(D_32, '#skF_3') | ~r2_hidden('#skF_2', D_32) | ~v4_pre_topc(D_32, '#skF_1') | ~v3_pre_topc(D_32, '#skF_1') | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.63/1.33  tff(c_187, plain, (![D_63]: (r2_hidden(D_63, '#skF_3') | ~r2_hidden('#skF_2', D_63) | ~v4_pre_topc(D_63, '#skF_1') | ~v3_pre_topc(D_63, '#skF_1') | ~m1_subset_1(D_63, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_42])).
% 2.63/1.33  tff(c_195, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_151, c_187])).
% 2.63/1.33  tff(c_329, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_199, c_195])).
% 2.63/1.33  tff(c_330, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_329])).
% 2.63/1.33  tff(c_334, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_330])).
% 2.63/1.33  tff(c_338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_334])).
% 2.63/1.33  tff(c_339, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_329])).
% 2.63/1.33  tff(c_341, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_339])).
% 2.63/1.33  tff(c_344, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_341])).
% 2.63/1.33  tff(c_347, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_344])).
% 2.63/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.33  tff(c_55, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2])).
% 2.63/1.33  tff(c_351, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_347, c_55])).
% 2.63/1.33  tff(c_131, plain, (~m1_setfam_1('#skF_3', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_122])).
% 2.63/1.33  tff(c_360, plain, (~m1_setfam_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_351, c_131])).
% 2.63/1.33  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_360])).
% 2.63/1.33  tff(c_371, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_339])).
% 2.63/1.33  tff(c_390, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_371])).
% 2.63/1.33  tff(c_394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_390])).
% 2.63/1.33  tff(c_396, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_158])).
% 2.63/1.33  tff(c_16, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.63/1.33  tff(c_407, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_396, c_16])).
% 2.63/1.33  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_407])).
% 2.63/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.33  
% 2.63/1.33  Inference rules
% 2.63/1.33  ----------------------
% 2.63/1.33  #Ref     : 0
% 2.63/1.33  #Sup     : 56
% 2.63/1.33  #Fact    : 0
% 2.63/1.33  #Define  : 0
% 2.63/1.33  #Split   : 11
% 2.63/1.33  #Chain   : 0
% 2.63/1.33  #Close   : 0
% 2.63/1.33  
% 2.63/1.33  Ordering : KBO
% 2.63/1.33  
% 2.63/1.33  Simplification rules
% 2.63/1.33  ----------------------
% 2.63/1.33  #Subsume      : 13
% 2.63/1.33  #Demod        : 70
% 2.63/1.33  #Tautology    : 16
% 2.63/1.33  #SimpNegUnit  : 7
% 2.63/1.33  #BackRed      : 28
% 2.63/1.33  
% 2.63/1.33  #Partial instantiations: 0
% 2.63/1.33  #Strategies tried      : 1
% 2.63/1.33  
% 2.63/1.33  Timing (in seconds)
% 2.63/1.33  ----------------------
% 2.63/1.33  Preprocessing        : 0.31
% 2.63/1.33  Parsing              : 0.17
% 2.63/1.33  CNF conversion       : 0.02
% 2.63/1.33  Main loop            : 0.24
% 2.63/1.33  Inferencing          : 0.08
% 2.63/1.33  Reduction            : 0.08
% 2.63/1.33  Demodulation         : 0.05
% 2.63/1.33  BG Simplification    : 0.01
% 2.63/1.33  Subsumption          : 0.04
% 2.63/1.33  Abstraction          : 0.01
% 2.63/1.33  MUC search           : 0.00
% 2.63/1.33  Cooper               : 0.00
% 2.63/1.33  Total                : 0.59
% 2.63/1.33  Index Insertion      : 0.00
% 2.63/1.33  Index Deletion       : 0.00
% 2.63/1.33  Index Matching       : 0.00
% 2.63/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
