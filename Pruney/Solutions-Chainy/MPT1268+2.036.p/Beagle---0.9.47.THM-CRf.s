%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:51 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 173 expanded)
%              Number of leaves         :   26 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  182 ( 534 expanded)
%              Number of equality atoms :   30 (  72 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_77,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_36,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_161,plain,(
    ! [B_67,A_68] :
      ( v2_tops_1(B_67,A_68)
      | k1_tops_1(A_68,B_67) != k1_xboole_0
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_168,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_161])).

tff(c_172,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_168])).

tff(c_173,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_172])).

tff(c_151,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k1_tops_1(A_65,B_66),B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_156,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_151])).

tff(c_160,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_156])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_95,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,C_57)
      | ~ r1_tarski(B_58,C_57)
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_61,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_63,c_95])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_123,plain,(
    ! [A_3,A_61] :
      ( r1_tarski(A_3,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_3,A_61)
      | ~ r1_tarski(A_61,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_118,c_8])).

tff(c_175,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_160,c_123])).

tff(c_182,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_175])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    ! [C_46] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_46
      | ~ v3_pre_topc(C_46,'#skF_1')
      | ~ r1_tarski(C_46,'#skF_2')
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_196,plain,(
    ! [C_69] :
      ( k1_xboole_0 = C_69
      | ~ v3_pre_topc(C_69,'#skF_1')
      | ~ r1_tarski(C_69,'#skF_2')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54])).

tff(c_404,plain,(
    ! [A_88] :
      ( k1_xboole_0 = A_88
      | ~ v3_pre_topc(A_88,'#skF_1')
      | ~ r1_tarski(A_88,'#skF_2')
      | ~ r1_tarski(A_88,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_196])).

tff(c_415,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_182,c_404])).

tff(c_434,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_415])).

tff(c_435,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_434])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_384,plain,(
    ! [A_86,B_87] :
      ( k1_tops_1(A_86,k1_tops_1(A_86,B_87)) = k1_tops_1(A_86,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_389,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_384])).

tff(c_393,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_389])).

tff(c_20,plain,(
    ! [C_26,A_14,D_28,B_22] :
      ( v3_pre_topc(C_26,A_14)
      | k1_tops_1(A_14,C_26) != C_26
      | ~ m1_subset_1(D_28,k1_zfmisc_1(u1_struct_0(B_22)))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(B_22)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_842,plain,(
    ! [D_116,B_117] :
      ( ~ m1_subset_1(D_116,k1_zfmisc_1(u1_struct_0(B_117)))
      | ~ l1_pre_topc(B_117) ) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_849,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_842])).

tff(c_854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_849])).

tff(c_978,plain,(
    ! [C_126,A_127] :
      ( v3_pre_topc(C_126,A_127)
      | k1_tops_1(A_127,C_126) != C_126
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_991,plain,(
    ! [A_128,A_129] :
      ( v3_pre_topc(A_128,A_129)
      | k1_tops_1(A_129,A_128) != A_128
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | ~ r1_tarski(A_128,u1_struct_0(A_129)) ) ),
    inference(resolution,[status(thm)],[c_14,c_978])).

tff(c_1005,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) != k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_182,c_991])).

tff(c_1027,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_393,c_1005])).

tff(c_1029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_1027])).

tff(c_1030,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1031,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1033,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_38])).

tff(c_40,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1035,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_40])).

tff(c_42,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1037,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_42])).

tff(c_1297,plain,(
    ! [A_155,B_156] :
      ( k1_tops_1(A_155,B_156) = k1_xboole_0
      | ~ v2_tops_1(B_156,A_155)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1307,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1297])).

tff(c_1315,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1031,c_1307])).

tff(c_1569,plain,(
    ! [B_169,A_170,C_171] :
      ( r1_tarski(B_169,k1_tops_1(A_170,C_171))
      | ~ r1_tarski(B_169,C_171)
      | ~ v3_pre_topc(B_169,A_170)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1576,plain,(
    ! [B_169] :
      ( r1_tarski(B_169,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_169,'#skF_2')
      | ~ v3_pre_topc(B_169,'#skF_1')
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1569])).

tff(c_1678,plain,(
    ! [B_179] :
      ( r1_tarski(B_179,k1_xboole_0)
      | ~ r1_tarski(B_179,'#skF_2')
      | ~ v3_pre_topc(B_179,'#skF_1')
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1315,c_1576])).

tff(c_1685,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1037,c_1678])).

tff(c_1692,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_1035,c_1685])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1052,plain,(
    ! [B_134,A_135] :
      ( B_134 = A_135
      | ~ r1_tarski(B_134,A_135)
      | ~ r1_tarski(A_135,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1070,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_1052])).

tff(c_1707,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1692,c_1070])).

tff(c_1725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1030,c_1707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.58  
% 3.55/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.58  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.55/1.58  
% 3.55/1.58  %Foreground sorts:
% 3.55/1.58  
% 3.55/1.58  
% 3.55/1.58  %Background operators:
% 3.55/1.58  
% 3.55/1.58  
% 3.55/1.58  %Foreground operators:
% 3.55/1.58  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.55/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.58  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.55/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.55/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.58  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.55/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.55/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.55/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.58  
% 3.55/1.60  tff(f_119, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 3.55/1.60  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.55/1.60  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.55/1.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.55/1.60  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.55/1.60  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.55/1.60  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 3.55/1.60  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 3.55/1.60  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.55/1.60  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.55/1.60  tff(c_36, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.55/1.60  tff(c_58, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.55/1.60  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.55/1.60  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.55/1.60  tff(c_161, plain, (![B_67, A_68]: (v2_tops_1(B_67, A_68) | k1_tops_1(A_68, B_67)!=k1_xboole_0 | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.55/1.60  tff(c_168, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_161])).
% 3.55/1.60  tff(c_172, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_168])).
% 3.55/1.60  tff(c_173, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_172])).
% 3.55/1.60  tff(c_151, plain, (![A_65, B_66]: (r1_tarski(k1_tops_1(A_65, B_66), B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.60  tff(c_156, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_151])).
% 3.55/1.60  tff(c_160, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_156])).
% 3.55/1.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.60  tff(c_59, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.55/1.60  tff(c_63, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_59])).
% 3.55/1.60  tff(c_95, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, C_57) | ~r1_tarski(B_58, C_57) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.55/1.60  tff(c_118, plain, (![A_61]: (r1_tarski(A_61, u1_struct_0('#skF_1')) | ~r1_tarski(A_61, '#skF_2'))), inference(resolution, [status(thm)], [c_63, c_95])).
% 3.55/1.60  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.55/1.60  tff(c_123, plain, (![A_3, A_61]: (r1_tarski(A_3, u1_struct_0('#skF_1')) | ~r1_tarski(A_3, A_61) | ~r1_tarski(A_61, '#skF_2'))), inference(resolution, [status(thm)], [c_118, c_8])).
% 3.55/1.60  tff(c_175, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_160, c_123])).
% 3.55/1.60  tff(c_182, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_175])).
% 3.55/1.60  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.55/1.60  tff(c_54, plain, (![C_46]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_46 | ~v3_pre_topc(C_46, '#skF_1') | ~r1_tarski(C_46, '#skF_2') | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.55/1.60  tff(c_196, plain, (![C_69]: (k1_xboole_0=C_69 | ~v3_pre_topc(C_69, '#skF_1') | ~r1_tarski(C_69, '#skF_2') | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_54])).
% 3.55/1.60  tff(c_404, plain, (![A_88]: (k1_xboole_0=A_88 | ~v3_pre_topc(A_88, '#skF_1') | ~r1_tarski(A_88, '#skF_2') | ~r1_tarski(A_88, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_196])).
% 3.55/1.60  tff(c_415, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_182, c_404])).
% 3.55/1.60  tff(c_434, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_415])).
% 3.55/1.60  tff(c_435, plain, (~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_173, c_434])).
% 3.55/1.60  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.55/1.60  tff(c_384, plain, (![A_86, B_87]: (k1_tops_1(A_86, k1_tops_1(A_86, B_87))=k1_tops_1(A_86, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.60  tff(c_389, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_384])).
% 3.55/1.60  tff(c_393, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_389])).
% 3.55/1.60  tff(c_20, plain, (![C_26, A_14, D_28, B_22]: (v3_pre_topc(C_26, A_14) | k1_tops_1(A_14, C_26)!=C_26 | ~m1_subset_1(D_28, k1_zfmisc_1(u1_struct_0(B_22))) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(B_22) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.55/1.60  tff(c_842, plain, (![D_116, B_117]: (~m1_subset_1(D_116, k1_zfmisc_1(u1_struct_0(B_117))) | ~l1_pre_topc(B_117))), inference(splitLeft, [status(thm)], [c_20])).
% 3.55/1.60  tff(c_849, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_842])).
% 3.55/1.60  tff(c_854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_849])).
% 3.55/1.60  tff(c_978, plain, (![C_126, A_127]: (v3_pre_topc(C_126, A_127) | k1_tops_1(A_127, C_126)!=C_126 | ~m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(splitRight, [status(thm)], [c_20])).
% 3.55/1.60  tff(c_991, plain, (![A_128, A_129]: (v3_pre_topc(A_128, A_129) | k1_tops_1(A_129, A_128)!=A_128 | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | ~r1_tarski(A_128, u1_struct_0(A_129)))), inference(resolution, [status(thm)], [c_14, c_978])).
% 3.55/1.60  tff(c_1005, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))!=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_182, c_991])).
% 3.55/1.60  tff(c_1027, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_393, c_1005])).
% 3.55/1.60  tff(c_1029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_1027])).
% 3.55/1.60  tff(c_1030, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.55/1.60  tff(c_1031, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.55/1.60  tff(c_38, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.55/1.60  tff(c_1033, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_38])).
% 3.55/1.60  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.55/1.60  tff(c_1035, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_40])).
% 3.55/1.60  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.55/1.60  tff(c_1037, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_42])).
% 3.55/1.60  tff(c_1297, plain, (![A_155, B_156]: (k1_tops_1(A_155, B_156)=k1_xboole_0 | ~v2_tops_1(B_156, A_155) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.55/1.60  tff(c_1307, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1297])).
% 3.55/1.60  tff(c_1315, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1031, c_1307])).
% 3.55/1.60  tff(c_1569, plain, (![B_169, A_170, C_171]: (r1_tarski(B_169, k1_tops_1(A_170, C_171)) | ~r1_tarski(B_169, C_171) | ~v3_pre_topc(B_169, A_170) | ~m1_subset_1(C_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.55/1.60  tff(c_1576, plain, (![B_169]: (r1_tarski(B_169, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_169, '#skF_2') | ~v3_pre_topc(B_169, '#skF_1') | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1569])).
% 3.55/1.60  tff(c_1678, plain, (![B_179]: (r1_tarski(B_179, k1_xboole_0) | ~r1_tarski(B_179, '#skF_2') | ~v3_pre_topc(B_179, '#skF_1') | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1315, c_1576])).
% 3.55/1.60  tff(c_1685, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1037, c_1678])).
% 3.55/1.60  tff(c_1692, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1033, c_1035, c_1685])).
% 3.55/1.60  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.55/1.60  tff(c_1052, plain, (![B_134, A_135]: (B_134=A_135 | ~r1_tarski(B_134, A_135) | ~r1_tarski(A_135, B_134))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.55/1.60  tff(c_1070, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_1052])).
% 3.55/1.60  tff(c_1707, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1692, c_1070])).
% 3.55/1.60  tff(c_1725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1030, c_1707])).
% 3.55/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.60  
% 3.55/1.60  Inference rules
% 3.55/1.60  ----------------------
% 3.55/1.60  #Ref     : 0
% 3.55/1.60  #Sup     : 344
% 3.55/1.60  #Fact    : 0
% 3.55/1.60  #Define  : 0
% 3.55/1.60  #Split   : 14
% 3.55/1.60  #Chain   : 0
% 3.55/1.60  #Close   : 0
% 3.55/1.60  
% 3.55/1.60  Ordering : KBO
% 3.55/1.60  
% 3.55/1.60  Simplification rules
% 3.55/1.60  ----------------------
% 3.55/1.60  #Subsume      : 120
% 3.55/1.60  #Demod        : 240
% 3.55/1.60  #Tautology    : 103
% 3.55/1.60  #SimpNegUnit  : 13
% 3.55/1.60  #BackRed      : 3
% 3.55/1.60  
% 3.55/1.60  #Partial instantiations: 0
% 3.55/1.60  #Strategies tried      : 1
% 3.55/1.60  
% 3.55/1.60  Timing (in seconds)
% 3.55/1.60  ----------------------
% 3.55/1.60  Preprocessing        : 0.35
% 3.55/1.60  Parsing              : 0.18
% 3.55/1.60  CNF conversion       : 0.03
% 3.55/1.60  Main loop            : 0.50
% 3.55/1.60  Inferencing          : 0.17
% 3.55/1.60  Reduction            : 0.16
% 3.55/1.60  Demodulation         : 0.11
% 3.55/1.60  BG Simplification    : 0.02
% 3.55/1.60  Subsumption          : 0.11
% 3.55/1.60  Abstraction          : 0.02
% 3.55/1.60  MUC search           : 0.00
% 3.55/1.60  Cooper               : 0.00
% 3.55/1.60  Total                : 0.88
% 3.55/1.60  Index Insertion      : 0.00
% 3.55/1.60  Index Deletion       : 0.00
% 3.55/1.60  Index Matching       : 0.00
% 3.55/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
