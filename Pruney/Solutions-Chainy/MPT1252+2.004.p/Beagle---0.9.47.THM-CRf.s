%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:52 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 942 expanded)
%              Number of leaves         :   25 ( 330 expanded)
%              Depth                    :   20
%              Number of atoms          :  199 (2240 expanded)
%              Number of equality atoms :   23 ( 358 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(k2_tops_1(A,k2_tops_1(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_28,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    ! [A_27,B_29] :
      ( k9_subset_1(u1_struct_0(A_27),k2_pre_topc(A_27,B_29),k2_pre_topc(A_27,k3_subset_1(u1_struct_0(A_27),B_29))) = k2_tops_1(A_27,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k2_pre_topc(A_13,B_14),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ! [A_44,B_45] :
      ( k2_pre_topc(A_44,k2_pre_topc(A_44,B_45)) = k2_pre_topc(A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_74,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_80,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_74])).

tff(c_136,plain,(
    ! [A_59,B_60] :
      ( k9_subset_1(u1_struct_0(A_59),k2_pre_topc(A_59,B_60),k2_pre_topc(A_59,k3_subset_1(u1_struct_0(A_59),B_60))) = k2_tops_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_148,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_136])).

tff(c_152,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_148])).

tff(c_407,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_410,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_407])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_410])).

tff(c_416,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_221,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_tarski(k2_pre_topc(A_70,k9_subset_1(u1_struct_0(A_70),B_71,C_72)),k9_subset_1(u1_struct_0(A_70),k2_pre_topc(A_70,B_71),k2_pre_topc(A_70,C_72)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_238,plain,(
    ! [C_72] :
      ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_72)),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_72)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_221])).

tff(c_248,plain,(
    ! [C_72] :
      ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_72)),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_72)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_238])).

tff(c_1346,plain,(
    ! [C_104] :
      ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_104)),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',C_104)))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_248])).

tff(c_1407,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1346])).

tff(c_1434,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1407])).

tff(c_1622,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1434])).

tff(c_1625,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_1622])).

tff(c_1629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1625])).

tff(c_1631,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1434])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k2_pre_topc(A_15,k2_pre_topc(A_15,B_16)) = k2_pre_topc(A_15,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1637,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1631,c_18])).

tff(c_1648,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1637])).

tff(c_2042,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(k2_pre_topc(A_110,k2_tops_1(A_110,B_111)),k9_subset_1(u1_struct_0(A_110),k2_pre_topc(A_110,k2_pre_topc(A_110,B_111)),k2_pre_topc(A_110,k2_pre_topc(A_110,k3_subset_1(u1_struct_0(A_110),B_111)))))
      | ~ m1_subset_1(k2_pre_topc(A_110,k3_subset_1(u1_struct_0(A_110),B_111)),k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ m1_subset_1(k2_pre_topc(A_110,B_111),k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_221])).

tff(c_2142,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_2042])).

tff(c_2178,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_32,c_416,c_1648,c_2142])).

tff(c_2209,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2178])).

tff(c_2212,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_2209])).

tff(c_2216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1631,c_2212])).

tff(c_2217,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_2178])).

tff(c_2257,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2217])).

tff(c_2261,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2257])).

tff(c_57,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k2_tops_1(A_40,B_41),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    ! [B_19,A_17] :
      ( r1_tarski(B_19,k2_pre_topc(A_17,B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_116,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k2_tops_1(A_51,B_52),k2_pre_topc(A_51,k2_tops_1(A_51,B_52)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_57,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_51,B_52] :
      ( k2_pre_topc(A_51,k2_tops_1(A_51,B_52)) = k2_tops_1(A_51,B_52)
      | ~ r1_tarski(k2_pre_topc(A_51,k2_tops_1(A_51,B_52)),k2_tops_1(A_51,B_52))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_2265,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2261,c_119])).

tff(c_2272,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2265])).

tff(c_26,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_tops_1(A_30,B_31),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_157,plain,(
    ! [A_63,B_64] :
      ( k2_pre_topc(A_63,k2_pre_topc(A_63,k2_tops_1(A_63,B_64))) = k2_pre_topc(A_63,k2_tops_1(A_63,B_64))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_26,c_65])).

tff(c_166,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_157])).

tff(c_172,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_166])).

tff(c_612,plain,(
    ! [A_87,B_88] :
      ( k2_pre_topc(A_87,k2_pre_topc(A_87,k2_tops_1(A_87,k2_pre_topc(A_87,B_88)))) = k2_pre_topc(A_87,k2_tops_1(A_87,k2_pre_topc(A_87,B_88)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_16,c_157])).

tff(c_678,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))))) = k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_612])).

tff(c_698,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_172,c_678])).

tff(c_702,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_698])).

tff(c_705,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_702])).

tff(c_708,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_705])).

tff(c_711,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_708])).

tff(c_715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_711])).

tff(c_717,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_698])).

tff(c_14,plain,(
    ! [A_9,B_10,C_12] :
      ( r1_tarski(k3_subset_1(A_9,B_10),k3_subset_1(A_9,k9_subset_1(A_9,B_10,C_12)))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1556,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_105),k2_pre_topc(A_105,B_106)),k3_subset_1(u1_struct_0(A_105),k2_tops_1(A_105,B_106)))
      | ~ m1_subset_1(k2_pre_topc(A_105,k3_subset_1(u1_struct_0(A_105),B_106)),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(k2_pre_topc(A_105,B_106),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_14])).

tff(c_1602,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_1556])).

tff(c_1619,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_717,c_717,c_172,c_1602])).

tff(c_1977,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1619])).

tff(c_1980,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1977])).

tff(c_1983,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1980])).

tff(c_1986,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_1983])).

tff(c_1990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_1986])).

tff(c_1991,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))))) ),
    inference(splitRight,[status(thm)],[c_1619])).

tff(c_10,plain,(
    ! [B_6,C_8,A_5] :
      ( r1_tarski(B_6,C_8)
      | ~ r1_tarski(k3_subset_1(A_5,C_8),k3_subset_1(A_5,B_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2020,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1991,c_10])).

tff(c_2029,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_2020])).

tff(c_2179,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2029])).

tff(c_2182,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_2179])).

tff(c_2186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_717,c_2182])).

tff(c_2187,plain,(
    r1_tarski(k2_tops_1('#skF_1',k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2029])).

tff(c_2278,plain,(
    r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2272,c_2272,c_2187])).

tff(c_2290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.86  
% 4.82/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.86  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.82/1.86  
% 4.82/1.86  %Foreground sorts:
% 4.82/1.86  
% 4.82/1.86  
% 4.82/1.86  %Background operators:
% 4.82/1.86  
% 4.82/1.86  
% 4.82/1.86  %Foreground operators:
% 4.82/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.86  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.82/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.82/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.82/1.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.82/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.82/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.82/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.82/1.86  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.82/1.86  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.82/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.86  
% 4.82/1.87  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_tops_1(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tops_1)).
% 4.82/1.87  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 4.82/1.87  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.82/1.87  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.82/1.87  tff(f_63, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 4.82/1.87  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 4.82/1.87  tff(f_93, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.82/1.87  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.82/1.87  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.82/1.87  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 4.82/1.87  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 4.82/1.87  tff(c_28, plain, (~r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.82/1.87  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.82/1.87  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.82/1.87  tff(c_24, plain, (![A_27, B_29]: (k9_subset_1(u1_struct_0(A_27), k2_pre_topc(A_27, B_29), k2_pre_topc(A_27, k3_subset_1(u1_struct_0(A_27), B_29)))=k2_tops_1(A_27, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.82/1.87  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.82/1.87  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(k2_pre_topc(A_13, B_14), k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.82/1.87  tff(c_65, plain, (![A_44, B_45]: (k2_pre_topc(A_44, k2_pre_topc(A_44, B_45))=k2_pre_topc(A_44, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.82/1.87  tff(c_74, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_65])).
% 4.82/1.87  tff(c_80, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_74])).
% 4.82/1.87  tff(c_136, plain, (![A_59, B_60]: (k9_subset_1(u1_struct_0(A_59), k2_pre_topc(A_59, B_60), k2_pre_topc(A_59, k3_subset_1(u1_struct_0(A_59), B_60)))=k2_tops_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.82/1.87  tff(c_148, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_80, c_136])).
% 4.82/1.87  tff(c_152, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_148])).
% 4.82/1.87  tff(c_407, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_152])).
% 4.82/1.87  tff(c_410, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_407])).
% 4.82/1.87  tff(c_414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_410])).
% 4.82/1.87  tff(c_416, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_152])).
% 4.82/1.87  tff(c_221, plain, (![A_70, B_71, C_72]: (r1_tarski(k2_pre_topc(A_70, k9_subset_1(u1_struct_0(A_70), B_71, C_72)), k9_subset_1(u1_struct_0(A_70), k2_pre_topc(A_70, B_71), k2_pre_topc(A_70, C_72))) | ~m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.82/1.87  tff(c_238, plain, (![C_72]: (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_72)), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', C_72))) | ~m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_221])).
% 4.82/1.87  tff(c_248, plain, (![C_72]: (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_72)), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', C_72))) | ~m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_238])).
% 4.82/1.87  tff(c_1346, plain, (![C_104]: (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_104)), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', C_104))) | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_416, c_248])).
% 4.82/1.87  tff(c_1407, plain, (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1346])).
% 4.82/1.87  tff(c_1434, plain, (r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1407])).
% 4.82/1.87  tff(c_1622, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1434])).
% 4.82/1.87  tff(c_1625, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_1622])).
% 4.82/1.87  tff(c_1629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1625])).
% 4.82/1.87  tff(c_1631, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1434])).
% 4.82/1.87  tff(c_18, plain, (![A_15, B_16]: (k2_pre_topc(A_15, k2_pre_topc(A_15, B_16))=k2_pre_topc(A_15, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.82/1.87  tff(c_1637, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1631, c_18])).
% 4.82/1.87  tff(c_1648, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1637])).
% 4.82/1.87  tff(c_2042, plain, (![A_110, B_111]: (r1_tarski(k2_pre_topc(A_110, k2_tops_1(A_110, B_111)), k9_subset_1(u1_struct_0(A_110), k2_pre_topc(A_110, k2_pre_topc(A_110, B_111)), k2_pre_topc(A_110, k2_pre_topc(A_110, k3_subset_1(u1_struct_0(A_110), B_111))))) | ~m1_subset_1(k2_pre_topc(A_110, k3_subset_1(u1_struct_0(A_110), B_111)), k1_zfmisc_1(u1_struct_0(A_110))) | ~m1_subset_1(k2_pre_topc(A_110, B_111), k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(superposition, [status(thm), theory('equality')], [c_24, c_221])).
% 4.82/1.87  tff(c_2142, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_80, c_2042])).
% 4.82/1.87  tff(c_2178, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_32, c_416, c_1648, c_2142])).
% 4.82/1.87  tff(c_2209, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2178])).
% 4.82/1.87  tff(c_2212, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_2209])).
% 4.82/1.87  tff(c_2216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1631, c_2212])).
% 4.82/1.87  tff(c_2217, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))), inference(splitRight, [status(thm)], [c_2178])).
% 4.82/1.87  tff(c_2257, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2217])).
% 4.82/1.87  tff(c_2261, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2257])).
% 4.82/1.87  tff(c_57, plain, (![A_40, B_41]: (m1_subset_1(k2_tops_1(A_40, B_41), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.82/1.87  tff(c_20, plain, (![B_19, A_17]: (r1_tarski(B_19, k2_pre_topc(A_17, B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.82/1.87  tff(c_116, plain, (![A_51, B_52]: (r1_tarski(k2_tops_1(A_51, B_52), k2_pre_topc(A_51, k2_tops_1(A_51, B_52))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_57, c_20])).
% 4.82/1.87  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.87  tff(c_119, plain, (![A_51, B_52]: (k2_pre_topc(A_51, k2_tops_1(A_51, B_52))=k2_tops_1(A_51, B_52) | ~r1_tarski(k2_pre_topc(A_51, k2_tops_1(A_51, B_52)), k2_tops_1(A_51, B_52)) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_116, c_2])).
% 4.82/1.87  tff(c_2265, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2261, c_119])).
% 4.82/1.87  tff(c_2272, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2265])).
% 4.82/1.87  tff(c_26, plain, (![A_30, B_31]: (m1_subset_1(k2_tops_1(A_30, B_31), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.82/1.87  tff(c_157, plain, (![A_63, B_64]: (k2_pre_topc(A_63, k2_pre_topc(A_63, k2_tops_1(A_63, B_64)))=k2_pre_topc(A_63, k2_tops_1(A_63, B_64)) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_26, c_65])).
% 4.82/1.87  tff(c_166, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_157])).
% 4.82/1.87  tff(c_172, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_166])).
% 4.82/1.87  tff(c_612, plain, (![A_87, B_88]: (k2_pre_topc(A_87, k2_pre_topc(A_87, k2_tops_1(A_87, k2_pre_topc(A_87, B_88))))=k2_pre_topc(A_87, k2_tops_1(A_87, k2_pre_topc(A_87, B_88))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_16, c_157])).
% 4.82/1.87  tff(c_678, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))))=k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_172, c_612])).
% 4.82/1.87  tff(c_698, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_172, c_678])).
% 4.82/1.88  tff(c_702, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_698])).
% 4.82/1.88  tff(c_705, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_702])).
% 4.82/1.88  tff(c_708, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_705])).
% 4.82/1.88  tff(c_711, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_708])).
% 4.82/1.88  tff(c_715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_711])).
% 4.82/1.88  tff(c_717, plain, (m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_698])).
% 4.82/1.88  tff(c_14, plain, (![A_9, B_10, C_12]: (r1_tarski(k3_subset_1(A_9, B_10), k3_subset_1(A_9, k9_subset_1(A_9, B_10, C_12))) | ~m1_subset_1(C_12, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.82/1.88  tff(c_1556, plain, (![A_105, B_106]: (r1_tarski(k3_subset_1(u1_struct_0(A_105), k2_pre_topc(A_105, B_106)), k3_subset_1(u1_struct_0(A_105), k2_tops_1(A_105, B_106))) | ~m1_subset_1(k2_pre_topc(A_105, k3_subset_1(u1_struct_0(A_105), B_106)), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(k2_pre_topc(A_105, B_106), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(superposition, [status(thm), theory('equality')], [c_136, c_14])).
% 4.82/1.88  tff(c_1602, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_172, c_1556])).
% 4.82/1.88  tff(c_1619, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_717, c_717, c_172, c_1602])).
% 4.82/1.88  tff(c_1977, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1619])).
% 4.82/1.88  tff(c_1980, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1977])).
% 4.82/1.88  tff(c_1983, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1980])).
% 4.82/1.88  tff(c_1986, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_1983])).
% 4.82/1.88  tff(c_1990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_717, c_1986])).
% 4.82/1.88  tff(c_1991, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))))), inference(splitRight, [status(thm)], [c_1619])).
% 4.82/1.88  tff(c_10, plain, (![B_6, C_8, A_5]: (r1_tarski(B_6, C_8) | ~r1_tarski(k3_subset_1(A_5, C_8), k3_subset_1(A_5, B_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.82/1.88  tff(c_2020, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1991, c_10])).
% 4.82/1.88  tff(c_2029, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_2020])).
% 4.82/1.88  tff(c_2179, plain, (~m1_subset_1(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2029])).
% 4.82/1.88  tff(c_2182, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_2179])).
% 4.82/1.88  tff(c_2186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_717, c_2182])).
% 4.82/1.88  tff(c_2187, plain, (r1_tarski(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_2029])).
% 4.82/1.88  tff(c_2278, plain, (r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2272, c_2272, c_2187])).
% 4.82/1.88  tff(c_2290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2278])).
% 4.82/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.88  
% 4.82/1.88  Inference rules
% 4.82/1.88  ----------------------
% 4.82/1.88  #Ref     : 0
% 4.82/1.88  #Sup     : 512
% 4.82/1.88  #Fact    : 0
% 4.82/1.88  #Define  : 0
% 4.82/1.88  #Split   : 11
% 4.82/1.88  #Chain   : 0
% 4.82/1.88  #Close   : 0
% 4.82/1.88  
% 4.82/1.88  Ordering : KBO
% 4.82/1.88  
% 4.82/1.88  Simplification rules
% 4.82/1.88  ----------------------
% 4.82/1.88  #Subsume      : 2
% 4.82/1.88  #Demod        : 602
% 4.82/1.88  #Tautology    : 195
% 4.82/1.88  #SimpNegUnit  : 1
% 4.82/1.88  #BackRed      : 15
% 4.82/1.88  
% 4.82/1.88  #Partial instantiations: 0
% 4.82/1.88  #Strategies tried      : 1
% 4.82/1.88  
% 4.82/1.88  Timing (in seconds)
% 4.82/1.88  ----------------------
% 4.82/1.88  Preprocessing        : 0.30
% 4.82/1.88  Parsing              : 0.17
% 4.82/1.88  CNF conversion       : 0.02
% 4.82/1.88  Main loop            : 0.81
% 4.82/1.88  Inferencing          : 0.26
% 4.82/1.88  Reduction            : 0.29
% 4.82/1.88  Demodulation         : 0.22
% 4.82/1.88  BG Simplification    : 0.04
% 4.82/1.88  Subsumption          : 0.17
% 4.82/1.88  Abstraction          : 0.04
% 4.82/1.88  MUC search           : 0.00
% 4.82/1.88  Cooper               : 0.00
% 4.82/1.88  Total                : 1.14
% 4.82/1.88  Index Insertion      : 0.00
% 4.82/1.88  Index Deletion       : 0.00
% 4.82/1.88  Index Matching       : 0.00
% 4.82/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
