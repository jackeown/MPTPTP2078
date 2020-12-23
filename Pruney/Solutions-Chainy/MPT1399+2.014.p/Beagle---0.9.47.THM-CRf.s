%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:20 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 234 expanded)
%              Number of leaves         :   40 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 ( 675 expanded)
%              Number of equality atoms :   17 (  93 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
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

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_60,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_58,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_64,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_36,plain,(
    ! [A_23] :
      ( v4_pre_topc(k2_struct_0(A_23),A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_108,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_114,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_32,c_108])).

tff(c_118,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_114])).

tff(c_34,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_123,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_34])).

tff(c_126,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_123])).

tff(c_140,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_143,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_140])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_143])).

tff(c_148,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_119,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_46])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_63,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_68,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_10])).

tff(c_183,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,B_59)
      | ~ r2_hidden(C_60,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_186,plain,(
    ! [C_60] : ~ r2_hidden(C_60,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_183])).

tff(c_54,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden('#skF_3',D_38)
      | ~ v4_pre_topc(D_38,'#skF_2')
      | ~ v3_pre_topc(D_38,'#skF_2')
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_324,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden('#skF_3',D_38)
      | ~ v4_pre_topc(D_38,'#skF_2')
      | ~ v3_pre_topc(D_38,'#skF_2')
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_54])).

tff(c_326,plain,(
    ! [D_80] :
      ( ~ r2_hidden('#skF_3',D_80)
      | ~ v4_pre_topc(D_80,'#skF_2')
      | ~ v3_pre_topc(D_80,'#skF_2')
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_324])).

tff(c_345,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_326])).

tff(c_355,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_69,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_22,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_61,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22])).

tff(c_272,plain,(
    ! [B_76,A_77] :
      ( v4_pre_topc(B_76,A_77)
      | ~ v1_xboole_0(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_283,plain,(
    ! [B_76] :
      ( v4_pre_topc(B_76,'#skF_2')
      | ~ v1_xboole_0(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_272])).

tff(c_301,plain,(
    ! [B_79] :
      ( v4_pre_topc(B_79,'#skF_2')
      | ~ v1_xboole_0(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_283])).

tff(c_317,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_61,c_301])).

tff(c_323,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_317])).

tff(c_14,plain,(
    ! [A_7] : k1_subset_1(A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_65,plain,(
    ! [A_7] : k1_subset_1(A_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_20,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_subset_1(A_10)) = k2_subset_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_subset_1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_66,plain,(
    ! [A_10] : k3_subset_1(A_10,'#skF_4') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64])).

tff(c_384,plain,(
    ! [A_87,B_88] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_87),B_88),A_87)
      | ~ v4_pre_topc(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_394,plain,(
    ! [A_87] :
      ( v3_pre_topc(u1_struct_0(A_87),A_87)
      | ~ v4_pre_topc('#skF_4',A_87)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_384])).

tff(c_406,plain,(
    ! [A_90] :
      ( v3_pre_topc(u1_struct_0(A_90),A_90)
      | ~ v4_pre_topc('#skF_4',A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_394])).

tff(c_412,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_406])).

tff(c_415,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_323,c_412])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_415])).

tff(c_418,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_421,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_424,plain,
    ( v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_421])).

tff(c_427,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_424])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_427])).

tff(c_430,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_434,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_430])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  
% 2.50/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.35  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.50/1.35  
% 2.50/1.35  %Foreground sorts:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Background operators:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Foreground operators:
% 2.50/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.50/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.50/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.50/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.35  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.50/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.50/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.50/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.35  
% 2.70/1.36  tff(f_148, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.70/1.36  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.70/1.36  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.70/1.36  tff(f_93, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.70/1.36  tff(f_105, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.70/1.36  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.70/1.36  tff(f_60, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.70/1.36  tff(f_62, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.70/1.36  tff(f_56, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.70/1.36  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.70/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.70/1.36  tff(f_66, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.70/1.36  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.70/1.36  tff(f_58, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.70/1.36  tff(f_64, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.70/1.36  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 2.70/1.36  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.70/1.36  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.70/1.36  tff(c_36, plain, (![A_23]: (v4_pre_topc(k2_struct_0(A_23), A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.70/1.36  tff(c_32, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.70/1.36  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.70/1.36  tff(c_108, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.70/1.36  tff(c_114, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_32, c_108])).
% 2.70/1.36  tff(c_118, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_114])).
% 2.70/1.36  tff(c_34, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.70/1.36  tff(c_123, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_34])).
% 2.70/1.36  tff(c_126, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_123])).
% 2.70/1.36  tff(c_140, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_126])).
% 2.70/1.36  tff(c_143, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_140])).
% 2.70/1.36  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_143])).
% 2.70/1.36  tff(c_148, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_126])).
% 2.70/1.36  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.70/1.36  tff(c_119, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_46])).
% 2.70/1.36  tff(c_24, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.70/1.36  tff(c_16, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.36  tff(c_18, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.36  tff(c_63, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.70/1.36  tff(c_42, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.70/1.36  tff(c_10, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.36  tff(c_68, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_10])).
% 2.70/1.36  tff(c_183, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, B_59) | ~r2_hidden(C_60, A_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.70/1.36  tff(c_186, plain, (![C_60]: (~r2_hidden(C_60, '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_183])).
% 2.70/1.36  tff(c_54, plain, (![D_38]: (r2_hidden(D_38, '#skF_4') | ~r2_hidden('#skF_3', D_38) | ~v4_pre_topc(D_38, '#skF_2') | ~v3_pre_topc(D_38, '#skF_2') | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.70/1.36  tff(c_324, plain, (![D_38]: (r2_hidden(D_38, '#skF_4') | ~r2_hidden('#skF_3', D_38) | ~v4_pre_topc(D_38, '#skF_2') | ~v3_pre_topc(D_38, '#skF_2') | ~m1_subset_1(D_38, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_54])).
% 2.70/1.36  tff(c_326, plain, (![D_80]: (~r2_hidden('#skF_3', D_80) | ~v4_pre_topc(D_80, '#skF_2') | ~v3_pre_topc(D_80, '#skF_2') | ~m1_subset_1(D_80, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_186, c_324])).
% 2.70/1.36  tff(c_345, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_63, c_326])).
% 2.70/1.36  tff(c_355, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_345])).
% 2.70/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.70/1.36  tff(c_69, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2])).
% 2.70/1.36  tff(c_22, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.70/1.36  tff(c_61, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22])).
% 2.70/1.36  tff(c_272, plain, (![B_76, A_77]: (v4_pre_topc(B_76, A_77) | ~v1_xboole_0(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.70/1.36  tff(c_283, plain, (![B_76]: (v4_pre_topc(B_76, '#skF_2') | ~v1_xboole_0(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_272])).
% 2.70/1.36  tff(c_301, plain, (![B_79]: (v4_pre_topc(B_79, '#skF_2') | ~v1_xboole_0(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_283])).
% 2.70/1.36  tff(c_317, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_61, c_301])).
% 2.70/1.36  tff(c_323, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_317])).
% 2.70/1.36  tff(c_14, plain, (![A_7]: (k1_subset_1(A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.70/1.36  tff(c_65, plain, (![A_7]: (k1_subset_1(A_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_14])).
% 2.70/1.36  tff(c_20, plain, (![A_10]: (k3_subset_1(A_10, k1_subset_1(A_10))=k2_subset_1(A_10))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.36  tff(c_64, plain, (![A_10]: (k3_subset_1(A_10, k1_subset_1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 2.70/1.36  tff(c_66, plain, (![A_10]: (k3_subset_1(A_10, '#skF_4')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64])).
% 2.70/1.36  tff(c_384, plain, (![A_87, B_88]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_87), B_88), A_87) | ~v4_pre_topc(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.70/1.36  tff(c_394, plain, (![A_87]: (v3_pre_topc(u1_struct_0(A_87), A_87) | ~v4_pre_topc('#skF_4', A_87) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(superposition, [status(thm), theory('equality')], [c_66, c_384])).
% 2.70/1.36  tff(c_406, plain, (![A_90]: (v3_pre_topc(u1_struct_0(A_90), A_90) | ~v4_pre_topc('#skF_4', A_90) | ~l1_pre_topc(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_394])).
% 2.70/1.36  tff(c_412, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_406])).
% 2.70/1.36  tff(c_415, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_323, c_412])).
% 2.70/1.36  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_355, c_415])).
% 2.70/1.36  tff(c_418, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_345])).
% 2.70/1.36  tff(c_421, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_418])).
% 2.70/1.36  tff(c_424, plain, (v1_xboole_0(k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_421])).
% 2.70/1.36  tff(c_427, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_424])).
% 2.70/1.36  tff(c_429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_427])).
% 2.70/1.36  tff(c_430, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_418])).
% 2.70/1.36  tff(c_434, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_430])).
% 2.70/1.36  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_434])).
% 2.70/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.36  
% 2.70/1.36  Inference rules
% 2.70/1.36  ----------------------
% 2.70/1.36  #Ref     : 0
% 2.70/1.36  #Sup     : 67
% 2.70/1.36  #Fact    : 0
% 2.70/1.36  #Define  : 0
% 2.70/1.36  #Split   : 5
% 2.70/1.36  #Chain   : 0
% 2.70/1.36  #Close   : 0
% 2.70/1.36  
% 2.70/1.36  Ordering : KBO
% 2.70/1.36  
% 2.70/1.36  Simplification rules
% 2.70/1.36  ----------------------
% 2.70/1.36  #Subsume      : 14
% 2.70/1.36  #Demod        : 42
% 2.70/1.36  #Tautology    : 22
% 2.70/1.36  #SimpNegUnit  : 4
% 2.70/1.36  #BackRed      : 1
% 2.70/1.36  
% 2.70/1.36  #Partial instantiations: 0
% 2.70/1.36  #Strategies tried      : 1
% 2.70/1.36  
% 2.70/1.36  Timing (in seconds)
% 2.70/1.36  ----------------------
% 2.70/1.37  Preprocessing        : 0.32
% 2.70/1.37  Parsing              : 0.16
% 2.70/1.37  CNF conversion       : 0.02
% 2.70/1.37  Main loop            : 0.23
% 2.70/1.37  Inferencing          : 0.08
% 2.70/1.37  Reduction            : 0.08
% 2.70/1.37  Demodulation         : 0.05
% 2.70/1.37  BG Simplification    : 0.01
% 2.70/1.37  Subsumption          : 0.04
% 2.70/1.37  Abstraction          : 0.01
% 2.70/1.37  MUC search           : 0.00
% 2.70/1.37  Cooper               : 0.00
% 2.70/1.37  Total                : 0.59
% 2.70/1.37  Index Insertion      : 0.00
% 2.70/1.37  Index Deletion       : 0.00
% 2.70/1.37  Index Matching       : 0.00
% 2.70/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
