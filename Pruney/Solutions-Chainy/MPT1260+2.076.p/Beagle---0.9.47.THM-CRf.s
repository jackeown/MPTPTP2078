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
% DateTime   : Thu Dec  3 10:21:10 EST 2020

% Result     : Theorem 31.74s
% Output     : CNFRefutation 31.76s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 749 expanded)
%              Number of leaves         :   38 ( 257 expanded)
%              Depth                    :   14
%              Number of atoms          :  222 (1630 expanded)
%              Number of equality atoms :   67 ( 412 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_81,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_394,plain,(
    ! [A_93,B_94,C_95] :
      ( k7_subset_1(A_93,B_94,C_95) = k4_xboole_0(B_94,C_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_405,plain,(
    ! [C_95] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_95) = k4_xboole_0('#skF_2',C_95) ),
    inference(resolution,[status(thm)],[c_42,c_394])).

tff(c_1104,plain,(
    ! [A_128,B_129] :
      ( k7_subset_1(u1_struct_0(A_128),B_129,k2_tops_1(A_128,B_129)) = k1_tops_1(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1138,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1104])).

tff(c_1169,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_405,c_1138])).

tff(c_499,plain,(
    ! [C_105] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_105) = k4_xboole_0('#skF_2',C_105) ),
    inference(resolution,[status(thm)],[c_42,c_394])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k7_subset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_505,plain,(
    ! [C_105] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_105),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_14])).

tff(c_511,plain,(
    ! [C_105] : m1_subset_1(k4_xboole_0('#skF_2',C_105),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_505])).

tff(c_1181,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1169,c_511])).

tff(c_36,plain,(
    ! [C_50,A_38,D_52,B_46] :
      ( v3_pre_topc(C_50,A_38)
      | k1_tops_1(A_38,C_50) != C_50
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0(B_46)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(B_46)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1514,plain,(
    ! [D_140,B_141] :
      ( ~ m1_subset_1(D_140,k1_zfmisc_1(u1_struct_0(B_141)))
      | ~ l1_pre_topc(B_141) ) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_1517,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1181,c_1514])).

tff(c_1566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1517])).

tff(c_1674,plain,(
    ! [C_143,A_144] :
      ( v3_pre_topc(C_143,A_144)
      | k1_tops_1(A_144,C_143) != C_143
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144) ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1725,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1674])).

tff(c_1760,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1725])).

tff(c_1761,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1760])).

tff(c_54,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_171,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_54])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_pre_topc(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_407,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1(k7_subset_1(A_96,B_97,C_98),k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_420,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_407])).

tff(c_1035,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_1038,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1035])).

tff(c_1045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1038])).

tff(c_1047,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5862,plain,(
    ! [C_266] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_266) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_266) ),
    inference(resolution,[status(thm)],[c_1047,c_20])).

tff(c_5899,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_5862])).

tff(c_560,plain,(
    ! [B_110,A_111] :
      ( r1_tarski(B_110,k2_pre_topc(A_111,B_110))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_574,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_560])).

tff(c_584,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_574])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_231,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = k3_subset_1(A_80,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_241,plain,(
    ! [B_27,A_26] :
      ( k4_xboole_0(B_27,A_26) = k3_subset_1(B_27,A_26)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_26,c_231])).

tff(c_589,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_584,c_241])).

tff(c_6079,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_589])).

tff(c_6,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_425,plain,(
    ! [A_99,C_100] : k7_subset_1(A_99,A_99,C_100) = k4_xboole_0(A_99,C_100) ),
    inference(resolution,[status(thm)],[c_55,c_394])).

tff(c_431,plain,(
    ! [A_99,C_100] :
      ( m1_subset_1(k4_xboole_0(A_99,C_100),k1_zfmisc_1(A_99))
      | ~ m1_subset_1(A_99,k1_zfmisc_1(A_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_14])).

tff(c_437,plain,(
    ! [A_99,C_100] : m1_subset_1(k4_xboole_0(A_99,C_100),k1_zfmisc_1(A_99)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_431])).

tff(c_1774,plain,(
    m1_subset_1(k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_437])).

tff(c_6145,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6079,c_1774])).

tff(c_141,plain,(
    ! [A_73,B_74] :
      ( k3_subset_1(A_73,k3_subset_1(A_73,B_74)) = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_148,plain,(
    ! [B_27,A_26] :
      ( k3_subset_1(B_27,k3_subset_1(B_27,A_26)) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_6160,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6079,c_148])).

tff(c_6166,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_6160])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6371,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6166,c_12])).

tff(c_6382,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6145,c_6371])).

tff(c_2083,plain,(
    ! [B_153,A_154,C_155] :
      ( k7_subset_1(B_153,A_154,C_155) = k4_xboole_0(A_154,C_155)
      | ~ r1_tarski(A_154,B_153) ) ),
    inference(resolution,[status(thm)],[c_26,c_394])).

tff(c_2155,plain,(
    ! [C_155] : k7_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2',C_155) = k4_xboole_0('#skF_2',C_155) ),
    inference(resolution,[status(thm)],[c_584,c_2083])).

tff(c_131,plain,(
    ! [A_70,B_71,C_72] :
      ( k9_subset_1(A_70,B_71,B_71) = B_71
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_140,plain,(
    ! [A_8,B_71] : k9_subset_1(A_8,B_71,B_71) = B_71 ),
    inference(resolution,[status(thm)],[c_55,c_131])).

tff(c_1252,plain,(
    ! [A_130,B_131,C_132] :
      ( k9_subset_1(A_130,B_131,k3_subset_1(A_130,C_132)) = k7_subset_1(A_130,B_131,C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(A_130))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10636,plain,(
    ! [A_355,B_356,B_357] :
      ( k9_subset_1(A_355,B_356,k3_subset_1(A_355,k3_subset_1(A_355,B_357))) = k7_subset_1(A_355,B_356,k3_subset_1(A_355,B_357))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(A_355))
      | ~ m1_subset_1(B_357,k1_zfmisc_1(A_355)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1252])).

tff(c_70187,plain,(
    ! [A_1075,B_1076] :
      ( k7_subset_1(A_1075,k3_subset_1(A_1075,k3_subset_1(A_1075,B_1076)),k3_subset_1(A_1075,B_1076)) = k3_subset_1(A_1075,k3_subset_1(A_1075,B_1076))
      | ~ m1_subset_1(k3_subset_1(A_1075,k3_subset_1(A_1075,B_1076)),k1_zfmisc_1(A_1075))
      | ~ m1_subset_1(B_1076,k1_zfmisc_1(A_1075)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_10636])).

tff(c_70233,plain,
    ( k7_subset_1(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')),k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')) = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6079,c_70187])).

tff(c_70304,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6382,c_6382,c_6166,c_6166,c_1169,c_2155,c_6166,c_6079,c_6079,c_6079,c_70233])).

tff(c_70306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1761,c_70304])).

tff(c_70307,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_70308,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_70617,plain,(
    ! [A_1106,B_1107,C_1108] :
      ( k7_subset_1(A_1106,B_1107,C_1108) = k4_xboole_0(B_1107,C_1108)
      | ~ m1_subset_1(B_1107,k1_zfmisc_1(A_1106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70628,plain,(
    ! [C_1108] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_1108) = k4_xboole_0('#skF_2',C_1108) ),
    inference(resolution,[status(thm)],[c_42,c_70617])).

tff(c_71372,plain,(
    ! [A_1147,B_1148] :
      ( k7_subset_1(u1_struct_0(A_1147),B_1148,k2_tops_1(A_1147,B_1148)) = k1_tops_1(A_1147,B_1148)
      | ~ m1_subset_1(B_1148,k1_zfmisc_1(u1_struct_0(A_1147)))
      | ~ l1_pre_topc(A_1147) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_71402,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_71372])).

tff(c_71427,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_70628,c_71402])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70629,plain,(
    ! [A_8,C_1108] : k7_subset_1(A_8,A_8,C_1108) = k4_xboole_0(A_8,C_1108) ),
    inference(resolution,[status(thm)],[c_55,c_70617])).

tff(c_70660,plain,(
    ! [A_1115,B_1116,C_1117] :
      ( m1_subset_1(k7_subset_1(A_1115,B_1116,C_1117),k1_zfmisc_1(A_1115))
      | ~ m1_subset_1(B_1116,k1_zfmisc_1(A_1115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70676,plain,(
    ! [A_8,C_1108] :
      ( m1_subset_1(k4_xboole_0(A_8,C_1108),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(A_8,k1_zfmisc_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70629,c_70660])).

tff(c_70685,plain,(
    ! [A_1118,C_1119] : m1_subset_1(k4_xboole_0(A_1118,C_1119),k1_zfmisc_1(A_1118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_70676])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k3_subset_1(A_6,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70690,plain,(
    ! [A_1118,C_1119] : k4_xboole_0(A_1118,k4_xboole_0(A_1118,C_1119)) = k3_subset_1(A_1118,k4_xboole_0(A_1118,C_1119)) ),
    inference(resolution,[status(thm)],[c_70685,c_8])).

tff(c_70716,plain,(
    ! [A_1118,C_1119] : k3_subset_1(A_1118,k4_xboole_0(A_1118,C_1119)) = k3_xboole_0(A_1118,C_1119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_70690])).

tff(c_71433,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_71427,c_70716])).

tff(c_70673,plain,(
    ! [C_1108] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_1108),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70628,c_70660])).

tff(c_70980,plain,(
    ! [C_1133] : m1_subset_1(k4_xboole_0('#skF_2',C_1133),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_70673])).

tff(c_71008,plain,(
    ! [B_4] : m1_subset_1(k3_xboole_0('#skF_2',B_4),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_70980])).

tff(c_72118,plain,(
    m1_subset_1(k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_71433,c_71008])).

tff(c_38,plain,(
    ! [B_46,D_52,C_50,A_38] :
      ( k1_tops_1(B_46,D_52) = D_52
      | ~ v3_pre_topc(D_52,B_46)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0(B_46)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(B_46)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_72241,plain,(
    ! [C_1167,A_1168] :
      ( ~ m1_subset_1(C_1167,k1_zfmisc_1(u1_struct_0(A_1168)))
      | ~ l1_pre_topc(A_1168)
      | ~ v2_pre_topc(A_1168) ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_72244,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72118,c_72241])).

tff(c_72293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_72244])).

tff(c_72395,plain,(
    ! [B_1169,D_1170] :
      ( k1_tops_1(B_1169,D_1170) = D_1170
      | ~ v3_pre_topc(D_1170,B_1169)
      | ~ m1_subset_1(D_1170,k1_zfmisc_1(u1_struct_0(B_1169)))
      | ~ l1_pre_topc(B_1169) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_72443,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_72395])).

tff(c_72475,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_70308,c_72443])).

tff(c_34,plain,(
    ! [A_35,B_37] :
      ( k7_subset_1(u1_struct_0(A_35),k2_pre_topc(A_35,B_37),k1_tops_1(A_35,B_37)) = k2_tops_1(A_35,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_72514,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_72475,c_34])).

tff(c_72518,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_72514])).

tff(c_72520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70307,c_72518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.74/22.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.76/22.47  
% 31.76/22.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.76/22.47  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 31.76/22.47  
% 31.76/22.47  %Foreground sorts:
% 31.76/22.47  
% 31.76/22.47  
% 31.76/22.47  %Background operators:
% 31.76/22.47  
% 31.76/22.47  
% 31.76/22.47  %Foreground operators:
% 31.76/22.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 31.76/22.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.76/22.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 31.76/22.47  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 31.76/22.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 31.76/22.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.76/22.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 31.76/22.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 31.76/22.47  tff('#skF_2', type, '#skF_2': $i).
% 31.76/22.47  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 31.76/22.47  tff('#skF_1', type, '#skF_1': $i).
% 31.76/22.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 31.76/22.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.76/22.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.76/22.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 31.76/22.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 31.76/22.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 31.76/22.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 31.76/22.47  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 31.76/22.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 31.76/22.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 31.76/22.47  
% 31.76/22.50  tff(f_136, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 31.76/22.50  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 31.76/22.50  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 31.76/22.50  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 31.76/22.50  tff(f_117, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 31.76/22.50  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 31.76/22.50  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 31.76/22.50  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 31.76/22.50  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 31.76/22.50  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 31.76/22.50  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 31.76/22.50  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 31.76/22.50  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 31.76/22.50  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 31.76/22.50  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 31.76/22.50  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 31.76/22.50  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 31.76/22.50  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.76/22.50  tff(c_81, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 31.76/22.50  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.76/22.50  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.76/22.50  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.76/22.50  tff(c_394, plain, (![A_93, B_94, C_95]: (k7_subset_1(A_93, B_94, C_95)=k4_xboole_0(B_94, C_95) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.76/22.50  tff(c_405, plain, (![C_95]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_95)=k4_xboole_0('#skF_2', C_95))), inference(resolution, [status(thm)], [c_42, c_394])).
% 31.76/22.50  tff(c_1104, plain, (![A_128, B_129]: (k7_subset_1(u1_struct_0(A_128), B_129, k2_tops_1(A_128, B_129))=k1_tops_1(A_128, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_124])).
% 31.76/22.50  tff(c_1138, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1104])).
% 31.76/22.50  tff(c_1169, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_405, c_1138])).
% 31.76/22.50  tff(c_499, plain, (![C_105]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_105)=k4_xboole_0('#skF_2', C_105))), inference(resolution, [status(thm)], [c_42, c_394])).
% 31.76/22.50  tff(c_14, plain, (![A_11, B_12, C_13]: (m1_subset_1(k7_subset_1(A_11, B_12, C_13), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 31.76/22.50  tff(c_505, plain, (![C_105]: (m1_subset_1(k4_xboole_0('#skF_2', C_105), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_499, c_14])).
% 31.76/22.50  tff(c_511, plain, (![C_105]: (m1_subset_1(k4_xboole_0('#skF_2', C_105), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_505])).
% 31.76/22.50  tff(c_1181, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1169, c_511])).
% 31.76/22.50  tff(c_36, plain, (![C_50, A_38, D_52, B_46]: (v3_pre_topc(C_50, A_38) | k1_tops_1(A_38, C_50)!=C_50 | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0(B_46))) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(B_46) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_117])).
% 31.76/22.50  tff(c_1514, plain, (![D_140, B_141]: (~m1_subset_1(D_140, k1_zfmisc_1(u1_struct_0(B_141))) | ~l1_pre_topc(B_141))), inference(splitLeft, [status(thm)], [c_36])).
% 31.76/22.50  tff(c_1517, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1181, c_1514])).
% 31.76/22.50  tff(c_1566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1517])).
% 31.76/22.50  tff(c_1674, plain, (![C_143, A_144]: (v3_pre_topc(C_143, A_144) | k1_tops_1(A_144, C_143)!=C_143 | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144))), inference(splitRight, [status(thm)], [c_36])).
% 31.76/22.50  tff(c_1725, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1674])).
% 31.76/22.50  tff(c_1760, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1725])).
% 31.76/22.50  tff(c_1761, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_81, c_1760])).
% 31.76/22.50  tff(c_54, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 31.76/22.50  tff(c_171, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_81, c_54])).
% 31.76/22.50  tff(c_28, plain, (![A_28, B_29]: (m1_subset_1(k2_pre_topc(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_74])).
% 31.76/22.50  tff(c_407, plain, (![A_96, B_97, C_98]: (m1_subset_1(k7_subset_1(A_96, B_97, C_98), k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 31.76/22.50  tff(c_420, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_171, c_407])).
% 31.76/22.50  tff(c_1035, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_420])).
% 31.76/22.50  tff(c_1038, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1035])).
% 31.76/22.50  tff(c_1045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1038])).
% 31.76/22.50  tff(c_1047, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_420])).
% 31.76/22.50  tff(c_20, plain, (![A_19, B_20, C_21]: (k7_subset_1(A_19, B_20, C_21)=k4_xboole_0(B_20, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.76/22.50  tff(c_5862, plain, (![C_266]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_266)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_266))), inference(resolution, [status(thm)], [c_1047, c_20])).
% 31.76/22.50  tff(c_5899, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_171, c_5862])).
% 31.76/22.50  tff(c_560, plain, (![B_110, A_111]: (r1_tarski(B_110, k2_pre_topc(A_111, B_110)) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_81])).
% 31.76/22.50  tff(c_574, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_560])).
% 31.76/22.50  tff(c_584, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_574])).
% 31.76/22.50  tff(c_26, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 31.76/22.50  tff(c_231, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=k3_subset_1(A_80, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 31.76/22.50  tff(c_241, plain, (![B_27, A_26]: (k4_xboole_0(B_27, A_26)=k3_subset_1(B_27, A_26) | ~r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_26, c_231])).
% 31.76/22.50  tff(c_589, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_584, c_241])).
% 31.76/22.50  tff(c_6079, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5899, c_589])).
% 31.76/22.50  tff(c_6, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 31.76/22.50  tff(c_10, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 31.76/22.50  tff(c_55, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 31.76/22.50  tff(c_425, plain, (![A_99, C_100]: (k7_subset_1(A_99, A_99, C_100)=k4_xboole_0(A_99, C_100))), inference(resolution, [status(thm)], [c_55, c_394])).
% 31.76/22.50  tff(c_431, plain, (![A_99, C_100]: (m1_subset_1(k4_xboole_0(A_99, C_100), k1_zfmisc_1(A_99)) | ~m1_subset_1(A_99, k1_zfmisc_1(A_99)))), inference(superposition, [status(thm), theory('equality')], [c_425, c_14])).
% 31.76/22.50  tff(c_437, plain, (![A_99, C_100]: (m1_subset_1(k4_xboole_0(A_99, C_100), k1_zfmisc_1(A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_431])).
% 31.76/22.50  tff(c_1774, plain, (m1_subset_1(k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_589, c_437])).
% 31.76/22.50  tff(c_6145, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6079, c_1774])).
% 31.76/22.50  tff(c_141, plain, (![A_73, B_74]: (k3_subset_1(A_73, k3_subset_1(A_73, B_74))=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 31.76/22.50  tff(c_148, plain, (![B_27, A_26]: (k3_subset_1(B_27, k3_subset_1(B_27, A_26))=A_26 | ~r1_tarski(A_26, B_27))), inference(resolution, [status(thm)], [c_26, c_141])).
% 31.76/22.50  tff(c_6160, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6079, c_148])).
% 31.76/22.50  tff(c_6166, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_584, c_6160])).
% 31.76/22.50  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 31.76/22.50  tff(c_6371, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6166, c_12])).
% 31.76/22.50  tff(c_6382, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6145, c_6371])).
% 31.76/22.50  tff(c_2083, plain, (![B_153, A_154, C_155]: (k7_subset_1(B_153, A_154, C_155)=k4_xboole_0(A_154, C_155) | ~r1_tarski(A_154, B_153))), inference(resolution, [status(thm)], [c_26, c_394])).
% 31.76/22.50  tff(c_2155, plain, (![C_155]: (k7_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2', C_155)=k4_xboole_0('#skF_2', C_155))), inference(resolution, [status(thm)], [c_584, c_2083])).
% 31.76/22.50  tff(c_131, plain, (![A_70, B_71, C_72]: (k9_subset_1(A_70, B_71, B_71)=B_71 | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 31.76/22.50  tff(c_140, plain, (![A_8, B_71]: (k9_subset_1(A_8, B_71, B_71)=B_71)), inference(resolution, [status(thm)], [c_55, c_131])).
% 31.76/22.50  tff(c_1252, plain, (![A_130, B_131, C_132]: (k9_subset_1(A_130, B_131, k3_subset_1(A_130, C_132))=k7_subset_1(A_130, B_131, C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(A_130)) | ~m1_subset_1(B_131, k1_zfmisc_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 31.76/22.50  tff(c_10636, plain, (![A_355, B_356, B_357]: (k9_subset_1(A_355, B_356, k3_subset_1(A_355, k3_subset_1(A_355, B_357)))=k7_subset_1(A_355, B_356, k3_subset_1(A_355, B_357)) | ~m1_subset_1(B_356, k1_zfmisc_1(A_355)) | ~m1_subset_1(B_357, k1_zfmisc_1(A_355)))), inference(resolution, [status(thm)], [c_12, c_1252])).
% 31.76/22.50  tff(c_70187, plain, (![A_1075, B_1076]: (k7_subset_1(A_1075, k3_subset_1(A_1075, k3_subset_1(A_1075, B_1076)), k3_subset_1(A_1075, B_1076))=k3_subset_1(A_1075, k3_subset_1(A_1075, B_1076)) | ~m1_subset_1(k3_subset_1(A_1075, k3_subset_1(A_1075, B_1076)), k1_zfmisc_1(A_1075)) | ~m1_subset_1(B_1076, k1_zfmisc_1(A_1075)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_10636])).
% 31.76/22.50  tff(c_70233, plain, (k7_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'))=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6079, c_70187])).
% 31.76/22.50  tff(c_70304, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6382, c_6382, c_6166, c_6166, c_1169, c_2155, c_6166, c_6079, c_6079, c_6079, c_70233])).
% 31.76/22.50  tff(c_70306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1761, c_70304])).
% 31.76/22.50  tff(c_70307, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 31.76/22.50  tff(c_70308, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 31.76/22.50  tff(c_70617, plain, (![A_1106, B_1107, C_1108]: (k7_subset_1(A_1106, B_1107, C_1108)=k4_xboole_0(B_1107, C_1108) | ~m1_subset_1(B_1107, k1_zfmisc_1(A_1106)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.76/22.50  tff(c_70628, plain, (![C_1108]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_1108)=k4_xboole_0('#skF_2', C_1108))), inference(resolution, [status(thm)], [c_42, c_70617])).
% 31.76/22.50  tff(c_71372, plain, (![A_1147, B_1148]: (k7_subset_1(u1_struct_0(A_1147), B_1148, k2_tops_1(A_1147, B_1148))=k1_tops_1(A_1147, B_1148) | ~m1_subset_1(B_1148, k1_zfmisc_1(u1_struct_0(A_1147))) | ~l1_pre_topc(A_1147))), inference(cnfTransformation, [status(thm)], [f_124])).
% 31.76/22.50  tff(c_71402, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_71372])).
% 31.76/22.50  tff(c_71427, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_70628, c_71402])).
% 31.76/22.50  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 31.76/22.50  tff(c_70629, plain, (![A_8, C_1108]: (k7_subset_1(A_8, A_8, C_1108)=k4_xboole_0(A_8, C_1108))), inference(resolution, [status(thm)], [c_55, c_70617])).
% 31.76/22.50  tff(c_70660, plain, (![A_1115, B_1116, C_1117]: (m1_subset_1(k7_subset_1(A_1115, B_1116, C_1117), k1_zfmisc_1(A_1115)) | ~m1_subset_1(B_1116, k1_zfmisc_1(A_1115)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 31.76/22.50  tff(c_70676, plain, (![A_8, C_1108]: (m1_subset_1(k4_xboole_0(A_8, C_1108), k1_zfmisc_1(A_8)) | ~m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_70629, c_70660])).
% 31.76/22.50  tff(c_70685, plain, (![A_1118, C_1119]: (m1_subset_1(k4_xboole_0(A_1118, C_1119), k1_zfmisc_1(A_1118)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_70676])).
% 31.76/22.50  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k3_subset_1(A_6, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 31.76/22.50  tff(c_70690, plain, (![A_1118, C_1119]: (k4_xboole_0(A_1118, k4_xboole_0(A_1118, C_1119))=k3_subset_1(A_1118, k4_xboole_0(A_1118, C_1119)))), inference(resolution, [status(thm)], [c_70685, c_8])).
% 31.76/22.50  tff(c_70716, plain, (![A_1118, C_1119]: (k3_subset_1(A_1118, k4_xboole_0(A_1118, C_1119))=k3_xboole_0(A_1118, C_1119))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_70690])).
% 31.76/22.50  tff(c_71433, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71427, c_70716])).
% 31.76/22.50  tff(c_70673, plain, (![C_1108]: (m1_subset_1(k4_xboole_0('#skF_2', C_1108), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_70628, c_70660])).
% 31.76/22.50  tff(c_70980, plain, (![C_1133]: (m1_subset_1(k4_xboole_0('#skF_2', C_1133), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_70673])).
% 31.76/22.50  tff(c_71008, plain, (![B_4]: (m1_subset_1(k3_xboole_0('#skF_2', B_4), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_70980])).
% 31.76/22.50  tff(c_72118, plain, (m1_subset_1(k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_71433, c_71008])).
% 31.76/22.50  tff(c_38, plain, (![B_46, D_52, C_50, A_38]: (k1_tops_1(B_46, D_52)=D_52 | ~v3_pre_topc(D_52, B_46) | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0(B_46))) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(B_46) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_117])).
% 31.76/22.50  tff(c_72241, plain, (![C_1167, A_1168]: (~m1_subset_1(C_1167, k1_zfmisc_1(u1_struct_0(A_1168))) | ~l1_pre_topc(A_1168) | ~v2_pre_topc(A_1168))), inference(splitLeft, [status(thm)], [c_38])).
% 31.76/22.50  tff(c_72244, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72118, c_72241])).
% 31.76/22.50  tff(c_72293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_72244])).
% 31.76/22.50  tff(c_72395, plain, (![B_1169, D_1170]: (k1_tops_1(B_1169, D_1170)=D_1170 | ~v3_pre_topc(D_1170, B_1169) | ~m1_subset_1(D_1170, k1_zfmisc_1(u1_struct_0(B_1169))) | ~l1_pre_topc(B_1169))), inference(splitRight, [status(thm)], [c_38])).
% 31.76/22.50  tff(c_72443, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_72395])).
% 31.76/22.50  tff(c_72475, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_70308, c_72443])).
% 31.76/22.50  tff(c_34, plain, (![A_35, B_37]: (k7_subset_1(u1_struct_0(A_35), k2_pre_topc(A_35, B_37), k1_tops_1(A_35, B_37))=k2_tops_1(A_35, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_96])).
% 31.76/22.50  tff(c_72514, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_72475, c_34])).
% 31.76/22.50  tff(c_72518, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_72514])).
% 31.76/22.50  tff(c_72520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70307, c_72518])).
% 31.76/22.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.76/22.50  
% 31.76/22.50  Inference rules
% 31.76/22.50  ----------------------
% 31.76/22.50  #Ref     : 0
% 31.76/22.50  #Sup     : 17396
% 31.76/22.50  #Fact    : 0
% 31.76/22.50  #Define  : 0
% 31.76/22.50  #Split   : 10
% 31.76/22.50  #Chain   : 0
% 31.76/22.50  #Close   : 0
% 31.76/22.50  
% 31.76/22.50  Ordering : KBO
% 31.76/22.50  
% 31.76/22.50  Simplification rules
% 31.76/22.50  ----------------------
% 31.76/22.50  #Subsume      : 288
% 31.76/22.50  #Demod        : 13810
% 31.76/22.50  #Tautology    : 5511
% 31.76/22.50  #SimpNegUnit  : 25
% 31.76/22.50  #BackRed      : 46
% 31.76/22.50  
% 31.76/22.50  #Partial instantiations: 0
% 31.76/22.50  #Strategies tried      : 1
% 31.76/22.50  
% 31.76/22.50  Timing (in seconds)
% 31.76/22.50  ----------------------
% 31.76/22.50  Preprocessing        : 0.34
% 31.76/22.50  Parsing              : 0.19
% 31.76/22.50  CNF conversion       : 0.02
% 31.76/22.50  Main loop            : 21.39
% 31.76/22.50  Inferencing          : 2.67
% 31.76/22.50  Reduction            : 12.65
% 31.76/22.50  Demodulation         : 11.24
% 31.76/22.50  BG Simplification    : 0.30
% 31.76/22.50  Subsumption          : 4.49
% 31.76/22.50  Abstraction          : 0.54
% 31.76/22.50  MUC search           : 0.00
% 31.76/22.50  Cooper               : 0.00
% 31.76/22.50  Total                : 21.77
% 31.76/22.50  Index Insertion      : 0.00
% 31.76/22.50  Index Deletion       : 0.00
% 31.76/22.50  Index Matching       : 0.00
% 31.76/22.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
