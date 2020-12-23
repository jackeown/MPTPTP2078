%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:26 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 303 expanded)
%              Number of leaves         :   38 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  150 ( 841 expanded)
%              Number of equality atoms :   16 ( 120 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

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

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ~ v2_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v2_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_34,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_2] : r1_tarski('#skF_4',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_24,plain,(
    ! [A_14] :
      ( v4_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_22,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_82,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_109,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_105])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_111,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_38])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_15] :
      ( v3_pre_topc(k2_struct_0(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_50,plain,(
    ! [D_30] :
      ( v4_pre_topc(D_30,'#skF_2')
      | ~ r2_hidden(D_30,'#skF_4')
      | ~ m1_subset_1(D_30,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_117,plain,(
    ! [D_45] :
      ( v4_pre_topc(D_45,'#skF_2')
      | ~ r2_hidden(D_45,'#skF_4')
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_50])).

tff(c_122,plain,
    ( v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_117])).

tff(c_439,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_46,plain,(
    ! [D_30] :
      ( r2_hidden(D_30,'#skF_4')
      | ~ r2_hidden('#skF_3',D_30)
      | ~ v4_pre_topc(D_30,'#skF_2')
      | ~ v3_pre_topc(D_30,'#skF_2')
      | ~ m1_subset_1(D_30,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_453,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,'#skF_4')
      | ~ r2_hidden('#skF_3',D_72)
      | ~ v4_pre_topc(D_72,'#skF_2')
      | ~ v3_pre_topc(D_72,'#skF_2')
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_46])).

tff(c_464,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),'#skF_4')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_453])).

tff(c_471,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_464])).

tff(c_616,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_619,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_616])).

tff(c_623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_619])).

tff(c_624,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_626,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_721,plain,
    ( v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_626])).

tff(c_724,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_721])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2])).

tff(c_728,plain,(
    k2_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_724,c_56])).

tff(c_32,plain,(
    ! [A_18] :
      ( ~ v2_tops_1(k2_struct_0(A_18),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_752,plain,
    ( ~ v2_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_32])).

tff(c_762,plain,
    ( ~ v2_tops_1('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_752])).

tff(c_763,plain,(
    ~ v2_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_762])).

tff(c_138,plain,(
    ! [A_48] :
      ( m1_subset_1('#skF_1'(A_48),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_144,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_138])).

tff(c_147,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_144])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_155,plain,(
    r1_tarski('#skF_1'('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_147,c_14])).

tff(c_741,plain,(
    r1_tarski('#skF_1'('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_155])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_6])).

tff(c_800,plain,(
    '#skF_1'('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_741,c_54])).

tff(c_28,plain,(
    ! [A_16] :
      ( v2_tops_1('#skF_1'(A_16),A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_818,plain,
    ( v2_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_28])).

tff(c_828,plain,(
    v2_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_818])).

tff(c_830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_763,c_828])).

tff(c_831,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_839,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_831])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_839])).

tff(c_845,plain,(
    r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_849,plain,(
    ~ r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_845,c_18])).

tff(c_853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_849])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.49  
% 3.14/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.49  %$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.14/1.49  
% 3.14/1.49  %Foreground sorts:
% 3.14/1.49  
% 3.14/1.49  
% 3.14/1.49  %Background operators:
% 3.14/1.49  
% 3.14/1.49  
% 3.14/1.49  %Foreground operators:
% 3.14/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.14/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.49  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.14/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.14/1.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.14/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.14/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.14/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.49  
% 3.14/1.51  tff(f_119, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 3.14/1.51  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.14/1.51  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 3.14/1.51  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.14/1.51  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.14/1.51  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.14/1.51  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.14/1.51  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.14/1.51  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.14/1.51  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.14/1.51  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => ~v2_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_tops_1)).
% 3.14/1.51  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v2_tops_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc5_tops_1)).
% 3.14/1.51  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.14/1.51  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.14/1.51  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.14/1.51  tff(c_34, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.14/1.51  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.51  tff(c_55, plain, (![A_2]: (r1_tarski('#skF_4', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4])).
% 3.14/1.51  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.14/1.51  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.14/1.51  tff(c_24, plain, (![A_14]: (v4_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.14/1.51  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.14/1.51  tff(c_22, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.51  tff(c_82, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.14/1.51  tff(c_105, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_22, c_82])).
% 3.14/1.51  tff(c_109, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_105])).
% 3.14/1.51  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.14/1.51  tff(c_111, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_38])).
% 3.14/1.51  tff(c_12, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.14/1.51  tff(c_26, plain, (![A_15]: (v3_pre_topc(k2_struct_0(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.14/1.51  tff(c_8, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.14/1.51  tff(c_10, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.14/1.51  tff(c_53, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.14/1.51  tff(c_50, plain, (![D_30]: (v4_pre_topc(D_30, '#skF_2') | ~r2_hidden(D_30, '#skF_4') | ~m1_subset_1(D_30, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.14/1.51  tff(c_117, plain, (![D_45]: (v4_pre_topc(D_45, '#skF_2') | ~r2_hidden(D_45, '#skF_4') | ~m1_subset_1(D_45, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_50])).
% 3.14/1.51  tff(c_122, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_53, c_117])).
% 3.14/1.51  tff(c_439, plain, (~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_122])).
% 3.14/1.51  tff(c_46, plain, (![D_30]: (r2_hidden(D_30, '#skF_4') | ~r2_hidden('#skF_3', D_30) | ~v4_pre_topc(D_30, '#skF_2') | ~v3_pre_topc(D_30, '#skF_2') | ~m1_subset_1(D_30, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.14/1.51  tff(c_453, plain, (![D_72]: (r2_hidden(D_72, '#skF_4') | ~r2_hidden('#skF_3', D_72) | ~v4_pre_topc(D_72, '#skF_2') | ~v3_pre_topc(D_72, '#skF_2') | ~m1_subset_1(D_72, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_46])).
% 3.14/1.51  tff(c_464, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_53, c_453])).
% 3.14/1.51  tff(c_471, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_439, c_464])).
% 3.14/1.51  tff(c_616, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_471])).
% 3.14/1.51  tff(c_619, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_616])).
% 3.14/1.51  tff(c_623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_619])).
% 3.14/1.51  tff(c_624, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_471])).
% 3.14/1.51  tff(c_626, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_624])).
% 3.14/1.51  tff(c_721, plain, (v1_xboole_0(k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_626])).
% 3.14/1.51  tff(c_724, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_721])).
% 3.14/1.51  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.51  tff(c_56, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2])).
% 3.14/1.51  tff(c_728, plain, (k2_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_724, c_56])).
% 3.14/1.51  tff(c_32, plain, (![A_18]: (~v2_tops_1(k2_struct_0(A_18), A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.14/1.51  tff(c_752, plain, (~v2_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_728, c_32])).
% 3.14/1.51  tff(c_762, plain, (~v2_tops_1('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_752])).
% 3.14/1.51  tff(c_763, plain, (~v2_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_762])).
% 3.14/1.51  tff(c_138, plain, (![A_48]: (m1_subset_1('#skF_1'(A_48), k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.51  tff(c_144, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_109, c_138])).
% 3.14/1.51  tff(c_147, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_144])).
% 3.14/1.51  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.14/1.51  tff(c_155, plain, (r1_tarski('#skF_1'('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_147, c_14])).
% 3.14/1.51  tff(c_741, plain, (r1_tarski('#skF_1'('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_728, c_155])).
% 3.14/1.51  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.51  tff(c_54, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_6])).
% 3.14/1.51  tff(c_800, plain, ('#skF_1'('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_741, c_54])).
% 3.14/1.51  tff(c_28, plain, (![A_16]: (v2_tops_1('#skF_1'(A_16), A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.51  tff(c_818, plain, (v2_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_800, c_28])).
% 3.14/1.51  tff(c_828, plain, (v2_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_818])).
% 3.14/1.51  tff(c_830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_763, c_828])).
% 3.14/1.51  tff(c_831, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_624])).
% 3.14/1.51  tff(c_839, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_831])).
% 3.14/1.51  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_839])).
% 3.14/1.51  tff(c_845, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_122])).
% 3.14/1.51  tff(c_18, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.14/1.51  tff(c_849, plain, (~r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_845, c_18])).
% 3.14/1.51  tff(c_853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_849])).
% 3.14/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.51  
% 3.14/1.51  Inference rules
% 3.14/1.51  ----------------------
% 3.14/1.51  #Ref     : 0
% 3.14/1.51  #Sup     : 130
% 3.14/1.51  #Fact    : 0
% 3.14/1.51  #Define  : 0
% 3.14/1.51  #Split   : 19
% 3.14/1.51  #Chain   : 0
% 3.14/1.51  #Close   : 0
% 3.14/1.51  
% 3.14/1.51  Ordering : KBO
% 3.14/1.51  
% 3.14/1.51  Simplification rules
% 3.14/1.51  ----------------------
% 3.14/1.51  #Subsume      : 36
% 3.14/1.51  #Demod        : 163
% 3.14/1.51  #Tautology    : 41
% 3.14/1.51  #SimpNegUnit  : 15
% 3.14/1.51  #BackRed      : 80
% 3.14/1.51  
% 3.14/1.51  #Partial instantiations: 0
% 3.14/1.51  #Strategies tried      : 1
% 3.14/1.51  
% 3.14/1.51  Timing (in seconds)
% 3.14/1.51  ----------------------
% 3.14/1.51  Preprocessing        : 0.34
% 3.14/1.51  Parsing              : 0.18
% 3.14/1.51  CNF conversion       : 0.02
% 3.14/1.51  Main loop            : 0.40
% 3.14/1.51  Inferencing          : 0.13
% 3.14/1.51  Reduction            : 0.13
% 3.14/1.51  Demodulation         : 0.09
% 3.14/1.51  BG Simplification    : 0.02
% 3.14/1.51  Subsumption          : 0.08
% 3.14/1.51  Abstraction          : 0.02
% 3.14/1.51  MUC search           : 0.00
% 3.14/1.51  Cooper               : 0.00
% 3.14/1.51  Total                : 0.78
% 3.14/1.51  Index Insertion      : 0.00
% 3.14/1.51  Index Deletion       : 0.00
% 3.14/1.51  Index Matching       : 0.00
% 3.14/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
