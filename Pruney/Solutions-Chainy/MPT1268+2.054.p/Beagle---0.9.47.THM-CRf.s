%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:54 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 154 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 ( 450 expanded)
%              Number of equality atoms :   29 (  68 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_106,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_32,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_51,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_325,plain,(
    ! [B_70,A_71] :
      ( v2_tops_1(B_70,A_71)
      | k1_tops_1(A_71,B_70) != k1_xboole_0
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_332,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_325])).

tff(c_336,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_332])).

tff(c_337,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_336])).

tff(c_60,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_60])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_152,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tops_1(A_60,B_61),B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_157,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_152])).

tff(c_161,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_157])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_467,plain,(
    ! [A_77,B_78] :
      ( v3_pre_topc(k1_tops_1(A_77,B_78),A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_472,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_467])).

tff(c_476,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_472])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(A_46,C_47)
      | ~ r1_tarski(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_46,B_2,A_1] :
      ( r1_tarski(A_46,B_2)
      | ~ r1_tarski(A_46,A_1)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_172,plain,(
    ! [B_2] :
      ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),B_2)
      | k4_xboole_0('#skF_2',B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_161,c_86])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    ! [C_35] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_35
      | ~ v3_pre_topc(C_35,'#skF_1')
      | ~ r1_tarski(C_35,'#skF_2')
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_273,plain,(
    ! [C_67] :
      ( k1_xboole_0 = C_67
      | ~ v3_pre_topc(C_67,'#skF_1')
      | ~ r1_tarski(C_67,'#skF_2')
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_50])).

tff(c_571,plain,(
    ! [A_85] :
      ( k1_xboole_0 = A_85
      | ~ v3_pre_topc(A_85,'#skF_1')
      | ~ r1_tarski(A_85,'#skF_2')
      | ~ r1_tarski(A_85,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_273])).

tff(c_575,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | k4_xboole_0('#skF_2',u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_172,c_571])).

tff(c_592,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_161,c_476,c_575])).

tff(c_594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_592])).

tff(c_595,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_596,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_38,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_609,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_38])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_613,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_609,c_12])).

tff(c_619,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = k1_xboole_0
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_632,plain,(
    k4_xboole_0('#skF_3',u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_613,c_619])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_xboole_0(k4_xboole_0(A_9,B_10),B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_659,plain,(
    r1_xboole_0(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_10])).

tff(c_734,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_xboole_0 = A_104
      | ~ r1_xboole_0(B_105,C_106)
      | ~ r1_tarski(A_104,C_106)
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1088,plain,(
    ! [A_129] :
      ( k1_xboole_0 = A_129
      | ~ r1_tarski(A_129,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_129,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_659,c_734])).

tff(c_1097,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_613,c_1088])).

tff(c_1109,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_1097])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_601,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_34])).

tff(c_36,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_599,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_36])).

tff(c_951,plain,(
    ! [A_116,B_117] :
      ( k1_tops_1(A_116,B_117) = k1_xboole_0
      | ~ v2_tops_1(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_961,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_951])).

tff(c_968,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_596,c_961])).

tff(c_1117,plain,(
    ! [B_130,A_131,C_132] :
      ( r1_tarski(B_130,k1_tops_1(A_131,C_132))
      | ~ r1_tarski(B_130,C_132)
      | ~ v3_pre_topc(B_130,A_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1124,plain,(
    ! [B_130] :
      ( r1_tarski(B_130,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_130,'#skF_2')
      | ~ v3_pre_topc(B_130,'#skF_1')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_1117])).

tff(c_1861,plain,(
    ! [B_158] :
      ( r1_tarski(B_158,k1_xboole_0)
      | ~ r1_tarski(B_158,'#skF_2')
      | ~ v3_pre_topc(B_158,'#skF_1')
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_968,c_1124])).

tff(c_1868,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_609,c_1861])).

tff(c_1875,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_599,c_1868])).

tff(c_1877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1109,c_1875])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.54  
% 3.55/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.54  %$ v3_pre_topc > v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.55/1.54  
% 3.55/1.54  %Foreground sorts:
% 3.55/1.54  
% 3.55/1.54  
% 3.55/1.54  %Background operators:
% 3.55/1.54  
% 3.55/1.54  
% 3.55/1.54  %Foreground operators:
% 3.55/1.54  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.55/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.54  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.55/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.55/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.54  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.55/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.55/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.55/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.55/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.55/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.54  
% 3.55/1.56  tff(f_106, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.55/1.56  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.55/1.56  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.55/1.56  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.55/1.56  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.55/1.56  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.55/1.56  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.55/1.56  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.55/1.56  tff(f_43, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 3.55/1.56  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.55/1.56  tff(c_32, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.55/1.56  tff(c_51, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 3.55/1.56  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.55/1.56  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.55/1.56  tff(c_325, plain, (![B_70, A_71]: (v2_tops_1(B_70, A_71) | k1_tops_1(A_71, B_70)!=k1_xboole_0 | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.55/1.56  tff(c_332, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_325])).
% 3.55/1.56  tff(c_336, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_332])).
% 3.55/1.56  tff(c_337, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_51, c_336])).
% 3.55/1.56  tff(c_60, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.56  tff(c_68, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_60])).
% 3.55/1.56  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.55/1.56  tff(c_72, plain, (k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_4])).
% 3.55/1.56  tff(c_152, plain, (![A_60, B_61]: (r1_tarski(k1_tops_1(A_60, B_61), B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.55/1.56  tff(c_157, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_152])).
% 3.55/1.56  tff(c_161, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_157])).
% 3.55/1.56  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.55/1.56  tff(c_467, plain, (![A_77, B_78]: (v3_pre_topc(k1_tops_1(A_77, B_78), A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.55/1.56  tff(c_472, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_467])).
% 3.55/1.56  tff(c_476, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_472])).
% 3.55/1.56  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.55/1.56  tff(c_80, plain, (![A_46, C_47, B_48]: (r1_tarski(A_46, C_47) | ~r1_tarski(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.55/1.56  tff(c_86, plain, (![A_46, B_2, A_1]: (r1_tarski(A_46, B_2) | ~r1_tarski(A_46, A_1) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_80])).
% 3.55/1.56  tff(c_172, plain, (![B_2]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), B_2) | k4_xboole_0('#skF_2', B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_161, c_86])).
% 3.55/1.56  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.56  tff(c_50, plain, (![C_35]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_35 | ~v3_pre_topc(C_35, '#skF_1') | ~r1_tarski(C_35, '#skF_2') | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.55/1.56  tff(c_273, plain, (![C_67]: (k1_xboole_0=C_67 | ~v3_pre_topc(C_67, '#skF_1') | ~r1_tarski(C_67, '#skF_2') | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_51, c_50])).
% 3.55/1.56  tff(c_571, plain, (![A_85]: (k1_xboole_0=A_85 | ~v3_pre_topc(A_85, '#skF_1') | ~r1_tarski(A_85, '#skF_2') | ~r1_tarski(A_85, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_273])).
% 3.55/1.56  tff(c_575, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | k4_xboole_0('#skF_2', u1_struct_0('#skF_1'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_172, c_571])).
% 3.55/1.56  tff(c_592, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_161, c_476, c_575])).
% 3.55/1.56  tff(c_594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_337, c_592])).
% 3.55/1.56  tff(c_595, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 3.55/1.56  tff(c_596, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 3.55/1.56  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.55/1.56  tff(c_609, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_596, c_38])).
% 3.55/1.56  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.55/1.56  tff(c_613, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_609, c_12])).
% 3.55/1.56  tff(c_619, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=k1_xboole_0 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.55/1.56  tff(c_632, plain, (k4_xboole_0('#skF_3', u1_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_613, c_619])).
% 3.55/1.56  tff(c_10, plain, (![A_9, B_10]: (r1_xboole_0(k4_xboole_0(A_9, B_10), B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.55/1.56  tff(c_659, plain, (r1_xboole_0(k1_xboole_0, u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_632, c_10])).
% 3.55/1.56  tff(c_734, plain, (![A_104, B_105, C_106]: (k1_xboole_0=A_104 | ~r1_xboole_0(B_105, C_106) | ~r1_tarski(A_104, C_106) | ~r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.55/1.56  tff(c_1088, plain, (![A_129]: (k1_xboole_0=A_129 | ~r1_tarski(A_129, u1_struct_0('#skF_1')) | ~r1_tarski(A_129, k1_xboole_0))), inference(resolution, [status(thm)], [c_659, c_734])).
% 3.55/1.56  tff(c_1097, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_613, c_1088])).
% 3.55/1.56  tff(c_1109, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_595, c_1097])).
% 3.55/1.56  tff(c_34, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.55/1.56  tff(c_601, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_596, c_34])).
% 3.55/1.56  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.55/1.56  tff(c_599, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_596, c_36])).
% 3.55/1.56  tff(c_951, plain, (![A_116, B_117]: (k1_tops_1(A_116, B_117)=k1_xboole_0 | ~v2_tops_1(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.55/1.56  tff(c_961, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_951])).
% 3.55/1.56  tff(c_968, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_596, c_961])).
% 3.55/1.56  tff(c_1117, plain, (![B_130, A_131, C_132]: (r1_tarski(B_130, k1_tops_1(A_131, C_132)) | ~r1_tarski(B_130, C_132) | ~v3_pre_topc(B_130, A_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.55/1.56  tff(c_1124, plain, (![B_130]: (r1_tarski(B_130, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_130, '#skF_2') | ~v3_pre_topc(B_130, '#skF_1') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1117])).
% 3.55/1.56  tff(c_1861, plain, (![B_158]: (r1_tarski(B_158, k1_xboole_0) | ~r1_tarski(B_158, '#skF_2') | ~v3_pre_topc(B_158, '#skF_1') | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_968, c_1124])).
% 3.55/1.56  tff(c_1868, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_609, c_1861])).
% 3.55/1.56  tff(c_1875, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_601, c_599, c_1868])).
% 3.55/1.56  tff(c_1877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1109, c_1875])).
% 3.55/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.56  
% 3.55/1.56  Inference rules
% 3.55/1.56  ----------------------
% 3.55/1.56  #Ref     : 0
% 3.55/1.56  #Sup     : 403
% 3.55/1.56  #Fact    : 0
% 3.55/1.56  #Define  : 0
% 3.55/1.56  #Split   : 9
% 3.55/1.56  #Chain   : 0
% 3.55/1.56  #Close   : 0
% 3.55/1.56  
% 3.55/1.56  Ordering : KBO
% 3.55/1.56  
% 3.55/1.56  Simplification rules
% 3.55/1.56  ----------------------
% 3.55/1.56  #Subsume      : 101
% 3.55/1.56  #Demod        : 135
% 3.55/1.56  #Tautology    : 129
% 3.55/1.56  #SimpNegUnit  : 31
% 3.55/1.56  #BackRed      : 3
% 3.55/1.56  
% 3.55/1.56  #Partial instantiations: 0
% 3.55/1.56  #Strategies tried      : 1
% 3.55/1.56  
% 3.55/1.56  Timing (in seconds)
% 3.55/1.56  ----------------------
% 3.55/1.56  Preprocessing        : 0.31
% 3.55/1.56  Parsing              : 0.17
% 3.55/1.56  CNF conversion       : 0.02
% 3.55/1.56  Main loop            : 0.52
% 3.55/1.56  Inferencing          : 0.19
% 3.55/1.56  Reduction            : 0.15
% 3.55/1.56  Demodulation         : 0.10
% 3.55/1.56  BG Simplification    : 0.02
% 3.55/1.56  Subsumption          : 0.12
% 3.55/1.56  Abstraction          : 0.02
% 3.55/1.56  MUC search           : 0.00
% 3.55/1.56  Cooper               : 0.00
% 3.55/1.56  Total                : 0.87
% 3.55/1.56  Index Insertion      : 0.00
% 3.55/1.56  Index Deletion       : 0.00
% 3.55/1.56  Index Matching       : 0.00
% 3.55/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
