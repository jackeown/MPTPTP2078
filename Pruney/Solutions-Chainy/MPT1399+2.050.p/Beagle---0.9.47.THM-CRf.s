%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:25 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 267 expanded)
%              Number of leaves         :   38 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 720 expanded)
%              Number of equality atoms :   24 ( 109 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_30,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_32,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_58,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    ! [A_22] :
      ( v4_pre_topc(k2_struct_0(A_22),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_59,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2])).

tff(c_24,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_100,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_24,c_93])).

tff(c_104,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_100])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_105,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_36])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_6,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_56,plain,(
    ! [A_2] : k1_subset_1(A_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = k2_subset_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_57,plain,(
    ! [A_5] : k3_subset_1(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55])).

tff(c_16,plain,(
    ! [C_13,A_7,B_11] :
      ( r2_hidden(C_13,k3_subset_1(A_7,B_11))
      | r2_hidden(C_13,B_11)
      | ~ m1_subset_1(C_13,A_7)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_7))
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_344,plain,(
    ! [C_67,A_68,B_69] :
      ( r2_hidden(C_67,k3_subset_1(A_68,B_69))
      | r2_hidden(C_67,B_69)
      | ~ m1_subset_1(C_67,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68))
      | A_68 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_353,plain,(
    ! [C_67,A_5] :
      ( r2_hidden(C_67,A_5)
      | r2_hidden(C_67,'#skF_3')
      | ~ m1_subset_1(C_67,A_5)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_5))
      | A_5 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_344])).

tff(c_374,plain,(
    ! [C_70,A_71] :
      ( r2_hidden(C_70,A_71)
      | r2_hidden(C_70,'#skF_3')
      | ~ m1_subset_1(C_70,A_71)
      | A_71 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_353])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_401,plain,(
    ! [C_70,A_71] :
      ( ~ r1_tarski('#skF_3',C_70)
      | r2_hidden(C_70,A_71)
      | ~ m1_subset_1(C_70,A_71)
      | A_71 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_374,c_20])).

tff(c_411,plain,(
    ! [C_70,A_71] :
      ( r2_hidden(C_70,A_71)
      | ~ m1_subset_1(C_70,A_71)
      | A_71 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_401])).

tff(c_30,plain,(
    ! [A_23] :
      ( v3_pre_topc(k2_struct_0(A_23),A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_48,plain,(
    ! [D_35] :
      ( v4_pre_topc(D_35,'#skF_1')
      | ~ r2_hidden(D_35,'#skF_3')
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_115,plain,(
    ! [D_48] :
      ( v4_pre_topc(D_48,'#skF_1')
      | ~ r2_hidden(D_48,'#skF_3')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_48])).

tff(c_124,plain,
    ( v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_144,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_44,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,'#skF_3')
      | ~ r2_hidden('#skF_2',D_35)
      | ~ v4_pre_topc(D_35,'#skF_1')
      | ~ v3_pre_topc(D_35,'#skF_1')
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_179,plain,(
    ! [D_60] :
      ( r2_hidden(D_60,'#skF_3')
      | ~ r2_hidden('#skF_2',D_60)
      | ~ v4_pre_topc(D_60,'#skF_1')
      | ~ v3_pre_topc(D_60,'#skF_1')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_44])).

tff(c_183,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_179])).

tff(c_190,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_183])).

tff(c_441,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_444,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_441])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_444])).

tff(c_449,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_457,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_460,plain,
    ( ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_411,c_457])).

tff(c_463,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_460])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_109,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_26])).

tff(c_112,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_109])).

tff(c_126,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_129,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_129])).

tff(c_134,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_476,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_134])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_476])).

tff(c_484,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_497,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_484])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_497])).

tff(c_503,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_518,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_503,c_20])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:29:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.44  
% 2.52/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.45  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.52/1.45  
% 2.52/1.45  %Foreground sorts:
% 2.52/1.45  
% 2.52/1.45  
% 2.52/1.45  %Background operators:
% 2.52/1.45  
% 2.52/1.45  
% 2.52/1.45  %Foreground operators:
% 2.52/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.52/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.52/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.52/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.52/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.52/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.52/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.45  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.52/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.52/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.52/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.52/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.52/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.52/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.45  
% 2.91/1.47  tff(f_119, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.91/1.47  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.91/1.47  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.91/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.91/1.47  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.91/1.47  tff(f_67, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.91/1.47  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.91/1.47  tff(f_30, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.91/1.47  tff(f_32, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.91/1.47  tff(f_36, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.91/1.47  tff(f_52, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 2.91/1.47  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.91/1.47  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.91/1.47  tff(f_34, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.91/1.47  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.91/1.47  tff(c_32, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.47  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.91/1.47  tff(c_58, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4])).
% 2.91/1.47  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.47  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.47  tff(c_28, plain, (![A_22]: (v4_pre_topc(k2_struct_0(A_22), A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.91/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.91/1.47  tff(c_59, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2])).
% 2.91/1.47  tff(c_24, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.91/1.47  tff(c_93, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.91/1.47  tff(c_100, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_24, c_93])).
% 2.91/1.47  tff(c_104, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_100])).
% 2.91/1.47  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.47  tff(c_105, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_36])).
% 2.91/1.47  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.91/1.47  tff(c_52, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 2.91/1.47  tff(c_6, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.91/1.47  tff(c_56, plain, (![A_2]: (k1_subset_1(A_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 2.91/1.47  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.47  tff(c_12, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=k2_subset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.91/1.47  tff(c_55, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 2.91/1.47  tff(c_57, plain, (![A_5]: (k3_subset_1(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_55])).
% 2.91/1.47  tff(c_16, plain, (![C_13, A_7, B_11]: (r2_hidden(C_13, k3_subset_1(A_7, B_11)) | r2_hidden(C_13, B_11) | ~m1_subset_1(C_13, A_7) | ~m1_subset_1(B_11, k1_zfmisc_1(A_7)) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.91/1.47  tff(c_344, plain, (![C_67, A_68, B_69]: (r2_hidden(C_67, k3_subset_1(A_68, B_69)) | r2_hidden(C_67, B_69) | ~m1_subset_1(C_67, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)) | A_68='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 2.91/1.47  tff(c_353, plain, (![C_67, A_5]: (r2_hidden(C_67, A_5) | r2_hidden(C_67, '#skF_3') | ~m1_subset_1(C_67, A_5) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_5)) | A_5='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_57, c_344])).
% 2.91/1.47  tff(c_374, plain, (![C_70, A_71]: (r2_hidden(C_70, A_71) | r2_hidden(C_70, '#skF_3') | ~m1_subset_1(C_70, A_71) | A_71='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_353])).
% 2.91/1.47  tff(c_20, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.91/1.47  tff(c_401, plain, (![C_70, A_71]: (~r1_tarski('#skF_3', C_70) | r2_hidden(C_70, A_71) | ~m1_subset_1(C_70, A_71) | A_71='#skF_3')), inference(resolution, [status(thm)], [c_374, c_20])).
% 2.91/1.47  tff(c_411, plain, (![C_70, A_71]: (r2_hidden(C_70, A_71) | ~m1_subset_1(C_70, A_71) | A_71='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_401])).
% 2.91/1.47  tff(c_30, plain, (![A_23]: (v3_pre_topc(k2_struct_0(A_23), A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.91/1.47  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.91/1.47  tff(c_54, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.91/1.47  tff(c_48, plain, (![D_35]: (v4_pre_topc(D_35, '#skF_1') | ~r2_hidden(D_35, '#skF_3') | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.47  tff(c_115, plain, (![D_48]: (v4_pre_topc(D_48, '#skF_1') | ~r2_hidden(D_48, '#skF_3') | ~m1_subset_1(D_48, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_48])).
% 2.91/1.47  tff(c_124, plain, (v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_54, c_115])).
% 2.91/1.47  tff(c_144, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_124])).
% 2.91/1.47  tff(c_44, plain, (![D_35]: (r2_hidden(D_35, '#skF_3') | ~r2_hidden('#skF_2', D_35) | ~v4_pre_topc(D_35, '#skF_1') | ~v3_pre_topc(D_35, '#skF_1') | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.47  tff(c_179, plain, (![D_60]: (r2_hidden(D_60, '#skF_3') | ~r2_hidden('#skF_2', D_60) | ~v4_pre_topc(D_60, '#skF_1') | ~v3_pre_topc(D_60, '#skF_1') | ~m1_subset_1(D_60, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_44])).
% 2.91/1.47  tff(c_183, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_54, c_179])).
% 2.91/1.47  tff(c_190, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_144, c_183])).
% 2.91/1.47  tff(c_441, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_190])).
% 2.91/1.47  tff(c_444, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_441])).
% 2.91/1.47  tff(c_448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_444])).
% 2.91/1.47  tff(c_449, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_190])).
% 2.91/1.47  tff(c_457, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_449])).
% 2.91/1.47  tff(c_460, plain, (~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | k2_struct_0('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_411, c_457])).
% 2.91/1.47  tff(c_463, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_460])).
% 2.91/1.47  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.91/1.47  tff(c_26, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.91/1.47  tff(c_109, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_104, c_26])).
% 2.91/1.47  tff(c_112, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_109])).
% 2.91/1.47  tff(c_126, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_112])).
% 2.91/1.47  tff(c_129, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_126])).
% 2.91/1.47  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_129])).
% 2.91/1.47  tff(c_134, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_112])).
% 2.91/1.47  tff(c_476, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_134])).
% 2.91/1.47  tff(c_483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_476])).
% 2.91/1.47  tff(c_484, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_449])).
% 2.91/1.47  tff(c_497, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_484])).
% 2.91/1.47  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_497])).
% 2.91/1.47  tff(c_503, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_124])).
% 2.91/1.47  tff(c_518, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_503, c_20])).
% 2.91/1.47  tff(c_522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_518])).
% 2.91/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.47  
% 2.91/1.47  Inference rules
% 2.91/1.47  ----------------------
% 2.91/1.47  #Ref     : 0
% 2.91/1.47  #Sup     : 74
% 2.91/1.47  #Fact    : 4
% 2.91/1.47  #Define  : 0
% 2.91/1.47  #Split   : 10
% 2.91/1.47  #Chain   : 0
% 2.91/1.47  #Close   : 0
% 2.91/1.47  
% 2.91/1.47  Ordering : KBO
% 2.91/1.47  
% 2.91/1.47  Simplification rules
% 2.91/1.47  ----------------------
% 2.91/1.47  #Subsume      : 9
% 2.91/1.47  #Demod        : 58
% 2.91/1.47  #Tautology    : 30
% 2.91/1.47  #SimpNegUnit  : 4
% 2.91/1.47  #BackRed      : 21
% 2.91/1.47  
% 2.91/1.47  #Partial instantiations: 0
% 2.91/1.47  #Strategies tried      : 1
% 2.91/1.47  
% 2.91/1.47  Timing (in seconds)
% 2.91/1.47  ----------------------
% 2.91/1.47  Preprocessing        : 0.34
% 2.91/1.47  Parsing              : 0.19
% 2.91/1.47  CNF conversion       : 0.02
% 2.91/1.47  Main loop            : 0.29
% 2.91/1.47  Inferencing          : 0.10
% 2.91/1.47  Reduction            : 0.09
% 2.91/1.47  Demodulation         : 0.06
% 2.91/1.47  BG Simplification    : 0.02
% 2.91/1.47  Subsumption          : 0.05
% 2.91/1.47  Abstraction          : 0.01
% 2.91/1.47  MUC search           : 0.00
% 2.91/1.47  Cooper               : 0.00
% 2.91/1.47  Total                : 0.67
% 2.91/1.47  Index Insertion      : 0.00
% 2.91/1.47  Index Deletion       : 0.00
% 2.91/1.47  Index Matching       : 0.00
% 2.91/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
