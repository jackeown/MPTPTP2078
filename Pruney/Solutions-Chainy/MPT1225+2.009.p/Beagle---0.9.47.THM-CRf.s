%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:28 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 185 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 ( 444 expanded)
%              Number of equality atoms :   24 (  83 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_79,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_40])).

tff(c_71,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_42,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_217,plain,(
    ! [A_67,A_68] :
      ( r1_tarski(A_67,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_67,A_68)
      | ~ r1_tarski(A_68,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_85,c_10])).

tff(c_242,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,B_4),u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_217])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_296,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(B_76,k2_pre_topc(A_77,B_76))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_304,plain,(
    ! [A_11,A_77] :
      ( r1_tarski(A_11,k2_pre_topc(A_77,A_11))
      | ~ l1_pre_topc(A_77)
      | ~ r1_tarski(A_11,u1_struct_0(A_77)) ) ),
    inference(resolution,[status(thm)],[c_16,c_296])).

tff(c_30,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_486,plain,(
    ! [A_87,B_88] :
      ( k2_pre_topc(A_87,B_88) = B_88
      | ~ v4_pre_topc(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_496,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_486])).

tff(c_503,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_496])).

tff(c_303,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_296])).

tff(c_310,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_303])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_336,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_310,c_2])).

tff(c_431,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_505,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_431])).

tff(c_511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_505])).

tff(c_512,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_152,plain,(
    ! [A_57,B_58,C_59] :
      ( k9_subset_1(A_57,B_58,C_59) = k3_xboole_0(B_58,C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_160,plain,(
    ! [B_58] : k9_subset_1(u1_struct_0('#skF_1'),B_58,'#skF_3') = k3_xboole_0(B_58,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_152])).

tff(c_28,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_394,plain,(
    ! [A_81,B_82] :
      ( k2_pre_topc(A_81,B_82) = B_82
      | ~ v4_pre_topc(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_401,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_394])).

tff(c_408,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_401])).

tff(c_301,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_296])).

tff(c_307,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_301])).

tff(c_323,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_307,c_2])).

tff(c_392,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_412,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_392])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_412])).

tff(c_419,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_162,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_26])).

tff(c_423,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_3') != k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_162])).

tff(c_425,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_3') != k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_423])).

tff(c_525,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_425])).

tff(c_1012,plain,(
    ! [A_135,B_136,C_137] :
      ( r1_tarski(k2_pre_topc(A_135,k9_subset_1(u1_struct_0(A_135),B_136,C_137)),k9_subset_1(u1_struct_0(A_135),k2_pre_topc(A_135,B_136),k2_pre_topc(A_135,C_137)))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1062,plain,(
    ! [B_58] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0(B_58,'#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_58),k2_pre_topc('#skF_1','#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_1012])).

tff(c_1376,plain,(
    ! [B_146] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0(B_146,'#skF_3')),k3_xboole_0(k2_pre_topc('#skF_1',B_146),'#skF_3'))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_160,c_419,c_1062])).

tff(c_1398,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_1376])).

tff(c_1411,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1398])).

tff(c_1434,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1411,c_2])).

tff(c_1448,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_1434])).

tff(c_1637,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_304,c_1448])).

tff(c_1640,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1637])).

tff(c_1709,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_242,c_1640])).

tff(c_1720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1709])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.72  
% 3.91/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.72  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.91/1.72  
% 3.91/1.72  %Foreground sorts:
% 3.91/1.72  
% 3.91/1.72  
% 3.91/1.72  %Background operators:
% 3.91/1.72  
% 3.91/1.72  
% 3.91/1.72  %Foreground operators:
% 3.91/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.91/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.91/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.91/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.72  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.91/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.91/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.91/1.72  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.91/1.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.91/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.72  
% 3.91/1.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.91/1.74  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.91/1.74  tff(f_94, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_1)).
% 3.91/1.74  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.91/1.74  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.91/1.74  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 3.91/1.74  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.91/1.74  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.91/1.74  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 3.91/1.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.74  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.91/1.74  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.91/1.74  tff(c_40, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.91/1.74  tff(c_48, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_40])).
% 3.91/1.74  tff(c_71, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.91/1.74  tff(c_85, plain, (![A_42]: (r1_tarski(A_42, u1_struct_0('#skF_1')) | ~r1_tarski(A_42, '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_71])).
% 3.91/1.74  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.91/1.74  tff(c_217, plain, (![A_67, A_68]: (r1_tarski(A_67, u1_struct_0('#skF_1')) | ~r1_tarski(A_67, A_68) | ~r1_tarski(A_68, '#skF_2'))), inference(resolution, [status(thm)], [c_85, c_10])).
% 3.91/1.74  tff(c_242, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), u1_struct_0('#skF_1')) | ~r1_tarski(A_3, '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_217])).
% 3.91/1.74  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.91/1.74  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.91/1.74  tff(c_296, plain, (![B_76, A_77]: (r1_tarski(B_76, k2_pre_topc(A_77, B_76)) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.91/1.74  tff(c_304, plain, (![A_11, A_77]: (r1_tarski(A_11, k2_pre_topc(A_77, A_11)) | ~l1_pre_topc(A_77) | ~r1_tarski(A_11, u1_struct_0(A_77)))), inference(resolution, [status(thm)], [c_16, c_296])).
% 3.91/1.74  tff(c_30, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.91/1.74  tff(c_486, plain, (![A_87, B_88]: (k2_pre_topc(A_87, B_88)=B_88 | ~v4_pre_topc(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.91/1.74  tff(c_496, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_486])).
% 3.91/1.74  tff(c_503, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_496])).
% 3.91/1.74  tff(c_303, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_296])).
% 3.91/1.74  tff(c_310, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_303])).
% 3.91/1.74  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.74  tff(c_336, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_310, c_2])).
% 3.91/1.74  tff(c_431, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_336])).
% 3.91/1.74  tff(c_505, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_431])).
% 3.91/1.74  tff(c_511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_505])).
% 3.91/1.74  tff(c_512, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_336])).
% 3.91/1.74  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.91/1.74  tff(c_152, plain, (![A_57, B_58, C_59]: (k9_subset_1(A_57, B_58, C_59)=k3_xboole_0(B_58, C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.91/1.74  tff(c_160, plain, (![B_58]: (k9_subset_1(u1_struct_0('#skF_1'), B_58, '#skF_3')=k3_xboole_0(B_58, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_152])).
% 3.91/1.74  tff(c_28, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.91/1.74  tff(c_394, plain, (![A_81, B_82]: (k2_pre_topc(A_81, B_82)=B_82 | ~v4_pre_topc(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.91/1.74  tff(c_401, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_394])).
% 3.91/1.74  tff(c_408, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_401])).
% 3.91/1.74  tff(c_301, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_296])).
% 3.91/1.74  tff(c_307, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_301])).
% 3.91/1.74  tff(c_323, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_307, c_2])).
% 3.91/1.74  tff(c_392, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_323])).
% 3.91/1.74  tff(c_412, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_392])).
% 3.91/1.74  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_412])).
% 3.91/1.74  tff(c_419, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_323])).
% 3.91/1.74  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.91/1.74  tff(c_162, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_26])).
% 3.91/1.74  tff(c_423, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_3')!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_162])).
% 3.91/1.74  tff(c_425, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_3')!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_423])).
% 3.91/1.74  tff(c_525, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_425])).
% 3.91/1.74  tff(c_1012, plain, (![A_135, B_136, C_137]: (r1_tarski(k2_pre_topc(A_135, k9_subset_1(u1_struct_0(A_135), B_136, C_137)), k9_subset_1(u1_struct_0(A_135), k2_pre_topc(A_135, B_136), k2_pre_topc(A_135, C_137))) | ~m1_subset_1(C_137, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.91/1.74  tff(c_1062, plain, (![B_58]: (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0(B_58, '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_58), k2_pre_topc('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_1012])).
% 3.91/1.74  tff(c_1376, plain, (![B_146]: (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0(B_146, '#skF_3')), k3_xboole_0(k2_pre_topc('#skF_1', B_146), '#skF_3')) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_160, c_419, c_1062])).
% 3.91/1.74  tff(c_1398, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_512, c_1376])).
% 3.91/1.74  tff(c_1411, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1398])).
% 3.91/1.74  tff(c_1434, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_2', '#skF_3') | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_1411, c_2])).
% 3.91/1.74  tff(c_1448, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_525, c_1434])).
% 3.91/1.74  tff(c_1637, plain, (~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_304, c_1448])).
% 3.91/1.74  tff(c_1640, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1637])).
% 3.91/1.74  tff(c_1709, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_242, c_1640])).
% 3.91/1.74  tff(c_1720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1709])).
% 3.91/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.74  
% 3.91/1.74  Inference rules
% 3.91/1.74  ----------------------
% 3.91/1.74  #Ref     : 0
% 3.91/1.74  #Sup     : 382
% 3.91/1.74  #Fact    : 0
% 3.91/1.74  #Define  : 0
% 3.91/1.74  #Split   : 5
% 3.91/1.74  #Chain   : 0
% 3.91/1.74  #Close   : 0
% 3.91/1.74  
% 3.91/1.74  Ordering : KBO
% 3.91/1.74  
% 3.91/1.74  Simplification rules
% 3.91/1.74  ----------------------
% 3.91/1.74  #Subsume      : 64
% 3.91/1.74  #Demod        : 244
% 3.91/1.74  #Tautology    : 82
% 3.91/1.74  #SimpNegUnit  : 1
% 3.91/1.74  #BackRed      : 12
% 3.91/1.74  
% 3.91/1.74  #Partial instantiations: 0
% 3.91/1.74  #Strategies tried      : 1
% 3.91/1.74  
% 3.91/1.74  Timing (in seconds)
% 3.91/1.74  ----------------------
% 3.91/1.74  Preprocessing        : 0.31
% 3.91/1.74  Parsing              : 0.16
% 3.91/1.74  CNF conversion       : 0.02
% 3.91/1.74  Main loop            : 0.61
% 3.91/1.74  Inferencing          : 0.20
% 3.91/1.74  Reduction            : 0.20
% 3.91/1.74  Demodulation         : 0.14
% 3.91/1.74  BG Simplification    : 0.03
% 3.91/1.74  Subsumption          : 0.14
% 3.91/1.74  Abstraction          : 0.04
% 3.91/1.74  MUC search           : 0.00
% 3.91/1.74  Cooper               : 0.00
% 3.91/1.74  Total                : 0.96
% 3.91/1.74  Index Insertion      : 0.00
% 3.91/1.74  Index Deletion       : 0.00
% 3.91/1.74  Index Matching       : 0.00
% 3.91/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
