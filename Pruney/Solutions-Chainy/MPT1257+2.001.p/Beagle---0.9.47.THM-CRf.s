%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:57 EST 2020

% Result     : Theorem 19.31s
% Output     : CNFRefutation 19.31s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 425 expanded)
%              Number of leaves         :   33 ( 154 expanded)
%              Depth                    :   15
%              Number of atoms          :  210 ( 895 expanded)
%              Number of equality atoms :   33 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_xboole_0(k1_tops_1(A,B),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_140,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(c_50,plain,(
    ~ r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [A_70,B_71] :
      ( k4_subset_1(A_70,B_71,k3_subset_1(A_70,B_71)) = k2_subset_1(A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_151,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_subset_1(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_142])).

tff(c_407,plain,(
    ! [A_89,B_90,C_91] :
      ( m1_subset_1(k4_subset_1(A_89,B_90,C_91),k1_zfmisc_1(A_89))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_613,plain,(
    ! [A_94,B_95,C_96] :
      ( r1_tarski(k4_subset_1(A_94,B_95,C_96),A_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_407,c_38])).

tff(c_634,plain,
    ( r1_tarski(k2_subset_1(u1_struct_0('#skF_1')),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_613])).

tff(c_650,plain,
    ( r1_tarski(k2_subset_1(u1_struct_0('#skF_1')),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_634])).

tff(c_651,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_650])).

tff(c_654,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_651])).

tff(c_661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_654])).

tff(c_663,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_650])).

tff(c_44,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k2_tops_1(A_46,B_47),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_20804,plain,(
    ! [A_447,B_448] :
      ( k4_subset_1(u1_struct_0(A_447),B_448,k2_tops_1(A_447,B_448)) = k2_pre_topc(A_447,B_448)
      | ~ m1_subset_1(B_448,k1_zfmisc_1(u1_struct_0(A_447)))
      | ~ l1_pre_topc(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_20827,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_20804])).

tff(c_20849,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_20827])).

tff(c_441,plain,(
    ! [A_89,B_90,C_91] :
      ( r1_tarski(k4_subset_1(A_89,B_90,C_91),A_89)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_407,c_38])).

tff(c_20853,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_20849,c_441])).

tff(c_20860,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20853])).

tff(c_20864,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_20860])).

tff(c_20867,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_20864])).

tff(c_20874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_20867])).

tff(c_20876,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_20860])).

tff(c_111,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k3_subset_1(A_64,B_65),k1_zfmisc_1(A_64))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k3_subset_1(A_64,B_65),A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(resolution,[status(thm)],[c_111,c_38])).

tff(c_120,plain,(
    ! [A_68,B_69] :
      ( k3_subset_1(A_68,k3_subset_1(A_68,B_69)) = B_69
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_129,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_120])).

tff(c_40,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_191,plain,(
    ! [B_74,A_75] :
      ( k4_subset_1(B_74,A_75,k3_subset_1(B_74,A_75)) = k2_subset_1(B_74)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_40,c_142])).

tff(c_203,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_2') = k2_subset_1(u1_struct_0('#skF_1'))
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_191])).

tff(c_222,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_225,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_115,c_222])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_225])).

tff(c_231,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_554,plain,(
    ! [A_92,B_93] :
      ( k2_tops_1(A_92,k3_subset_1(u1_struct_0(A_92),B_93)) = k2_tops_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_571,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_554])).

tff(c_584,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_571])).

tff(c_26078,plain,(
    ! [A_521,A_522] :
      ( k4_subset_1(u1_struct_0(A_521),A_522,k2_tops_1(A_521,A_522)) = k2_pre_topc(A_521,A_522)
      | ~ l1_pre_topc(A_521)
      | ~ r1_tarski(A_522,u1_struct_0(A_521)) ) ),
    inference(resolution,[status(thm)],[c_40,c_20804])).

tff(c_26121,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_26078])).

tff(c_26143,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_54,c_26121])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k4_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42324,plain,
    ( m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26143,c_12])).

tff(c_42356,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_20876,c_42324])).

tff(c_22270,plain,(
    ! [A_467,B_468] :
      ( k3_subset_1(u1_struct_0(A_467),k2_pre_topc(A_467,k3_subset_1(u1_struct_0(A_467),B_468))) = k1_tops_1(A_467,B_468)
      | ~ m1_subset_1(B_468,k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ l1_pre_topc(A_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_22329,plain,(
    ! [A_467,B_468] :
      ( m1_subset_1(k1_tops_1(A_467,B_468),k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ m1_subset_1(k2_pre_topc(A_467,k3_subset_1(u1_struct_0(A_467),B_468)),k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ m1_subset_1(B_468,k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ l1_pre_topc(A_467) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22270,c_10])).

tff(c_42500,plain,
    ( m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42356,c_22329])).

tff(c_42551,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42500])).

tff(c_20989,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20876,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_331,plain,(
    ! [A_84,B_85,C_86] :
      ( k4_subset_1(A_84,B_85,C_86) = k2_xboole_0(B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20469,plain,(
    ! [B_431,B_432,A_433] :
      ( k4_subset_1(B_431,B_432,A_433) = k2_xboole_0(B_432,A_433)
      | ~ m1_subset_1(B_432,k1_zfmisc_1(B_431))
      | ~ r1_tarski(A_433,B_431) ) ),
    inference(resolution,[status(thm)],[c_40,c_331])).

tff(c_51232,plain,(
    ! [A_807,B_808,A_809] :
      ( k4_subset_1(A_807,k3_subset_1(A_807,B_808),A_809) = k2_xboole_0(k3_subset_1(A_807,B_808),A_809)
      | ~ r1_tarski(A_809,A_807)
      | ~ m1_subset_1(B_808,k1_zfmisc_1(A_807)) ) ),
    inference(resolution,[status(thm)],[c_10,c_20469])).

tff(c_51453,plain,(
    ! [A_811] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_811) = k2_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_811)
      | ~ r1_tarski(A_811,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_51232])).

tff(c_51466,plain,
    ( k2_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_51453,c_26143])).

tff(c_51585,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20989,c_2,c_51466])).

tff(c_27364,plain,(
    ! [A_538,B_539,B_540] :
      ( k4_subset_1(A_538,B_539,k3_subset_1(A_538,B_540)) = k2_xboole_0(B_539,k3_subset_1(A_538,B_540))
      | ~ m1_subset_1(B_539,k1_zfmisc_1(A_538))
      | ~ m1_subset_1(B_540,k1_zfmisc_1(A_538)) ) ),
    inference(resolution,[status(thm)],[c_10,c_331])).

tff(c_51661,plain,(
    ! [B_812,A_813,B_814] :
      ( k4_subset_1(B_812,A_813,k3_subset_1(B_812,B_814)) = k2_xboole_0(A_813,k3_subset_1(B_812,B_814))
      | ~ m1_subset_1(B_814,k1_zfmisc_1(B_812))
      | ~ r1_tarski(A_813,B_812) ) ),
    inference(resolution,[status(thm)],[c_40,c_27364])).

tff(c_51927,plain,(
    ! [A_816] :
      ( k4_subset_1(u1_struct_0('#skF_1'),A_816,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_xboole_0(A_816,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
      | ~ r1_tarski(A_816,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_51661])).

tff(c_28,plain,(
    ! [A_29,B_30,C_32] :
      ( r1_tarski(k3_subset_1(A_29,k4_subset_1(A_29,B_30,C_32)),k3_subset_1(A_29,B_30))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22060,plain,(
    ! [B_464,C_465,A_466] :
      ( r1_tarski(B_464,C_465)
      | ~ r1_tarski(k3_subset_1(A_466,C_465),k3_subset_1(A_466,B_464))
      | ~ m1_subset_1(C_465,k1_zfmisc_1(A_466))
      | ~ m1_subset_1(B_464,k1_zfmisc_1(A_466)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_29344,plain,(
    ! [B_569,A_570,C_571] :
      ( r1_tarski(B_569,k4_subset_1(A_570,B_569,C_571))
      | ~ m1_subset_1(k4_subset_1(A_570,B_569,C_571),k1_zfmisc_1(A_570))
      | ~ m1_subset_1(C_571,k1_zfmisc_1(A_570))
      | ~ m1_subset_1(B_569,k1_zfmisc_1(A_570)) ) ),
    inference(resolution,[status(thm)],[c_28,c_22060])).

tff(c_29490,plain,(
    ! [B_8,A_7,C_9] :
      ( r1_tarski(B_8,k4_subset_1(A_7,B_8,C_9))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_12,c_29344])).

tff(c_51975,plain,(
    ! [A_816] :
      ( r1_tarski(A_816,k2_xboole_0(A_816,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(A_816,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_816,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51927,c_29490])).

tff(c_53757,plain,(
    ! [A_830] :
      ( r1_tarski(A_830,k2_xboole_0(A_830,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
      | ~ m1_subset_1(A_830,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_830,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_51975])).

tff(c_53782,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_51585,c_53757])).

tff(c_53812,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20989,c_20876,c_53782])).

tff(c_22,plain,(
    ! [A_17,C_20,B_18] :
      ( r1_tarski(k3_subset_1(A_17,C_20),k3_subset_1(A_17,B_18))
      | ~ r1_tarski(B_18,C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22287,plain,(
    ! [A_467,B_468,B_18] :
      ( r1_tarski(k1_tops_1(A_467,B_468),k3_subset_1(u1_struct_0(A_467),B_18))
      | ~ r1_tarski(B_18,k2_pre_topc(A_467,k3_subset_1(u1_struct_0(A_467),B_468)))
      | ~ m1_subset_1(k2_pre_topc(A_467,k3_subset_1(u1_struct_0(A_467),B_468)),k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ m1_subset_1(B_468,k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ l1_pre_topc(A_467) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22270,c_22])).

tff(c_53844,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_53812,c_22287])).

tff(c_53855,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_20876,c_42356,c_53844])).

tff(c_30,plain,(
    ! [B_34,C_36,A_33] :
      ( r1_xboole_0(B_34,C_36)
      | ~ r1_tarski(B_34,k3_subset_1(A_33,C_36))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54537,plain,
    ( r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_53855,c_30])).

tff(c_54550,plain,(
    r1_xboole_0(k1_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42551,c_20876,c_54537])).

tff(c_54552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_54550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.31/10.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.31/10.93  
% 19.31/10.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.31/10.93  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 19.31/10.93  
% 19.31/10.93  %Foreground sorts:
% 19.31/10.93  
% 19.31/10.93  
% 19.31/10.93  %Background operators:
% 19.31/10.93  
% 19.31/10.93  
% 19.31/10.93  %Foreground operators:
% 19.31/10.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.31/10.93  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 19.31/10.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.31/10.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.31/10.93  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 19.31/10.93  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 19.31/10.93  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 19.31/10.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 19.31/10.93  tff('#skF_2', type, '#skF_2': $i).
% 19.31/10.93  tff('#skF_1', type, '#skF_1': $i).
% 19.31/10.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.31/10.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.31/10.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.31/10.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.31/10.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.31/10.93  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 19.31/10.93  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 19.31/10.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.31/10.93  
% 19.31/10.95  tff(f_148, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_xboole_0(k1_tops_1(A, B), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_1)).
% 19.31/10.95  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 19.31/10.95  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 19.31/10.95  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 19.31/10.95  tff(f_113, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 19.31/10.95  tff(f_126, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 19.31/10.95  tff(f_140, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 19.31/10.95  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 19.31/10.95  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 19.31/10.95  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 19.31/10.95  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 19.31/10.95  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 19.31/10.95  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 19.31/10.95  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 19.31/10.95  tff(f_100, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 19.31/10.95  tff(c_50, plain, (~r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 19.31/10.95  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 19.31/10.95  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 19.31/10.95  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.31/10.95  tff(c_142, plain, (![A_70, B_71]: (k4_subset_1(A_70, B_71, k3_subset_1(A_70, B_71))=k2_subset_1(A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.31/10.95  tff(c_151, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_subset_1(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_142])).
% 19.31/10.95  tff(c_407, plain, (![A_89, B_90, C_91]: (m1_subset_1(k4_subset_1(A_89, B_90, C_91), k1_zfmisc_1(A_89)) | ~m1_subset_1(C_91, k1_zfmisc_1(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.31/10.95  tff(c_38, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 19.31/10.95  tff(c_613, plain, (![A_94, B_95, C_96]: (r1_tarski(k4_subset_1(A_94, B_95, C_96), A_94) | ~m1_subset_1(C_96, k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(resolution, [status(thm)], [c_407, c_38])).
% 19.31/10.95  tff(c_634, plain, (r1_tarski(k2_subset_1(u1_struct_0('#skF_1')), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_151, c_613])).
% 19.31/10.95  tff(c_650, plain, (r1_tarski(k2_subset_1(u1_struct_0('#skF_1')), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_634])).
% 19.31/10.95  tff(c_651, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_650])).
% 19.31/10.95  tff(c_654, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_651])).
% 19.31/10.95  tff(c_661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_654])).
% 19.31/10.95  tff(c_663, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_650])).
% 19.31/10.95  tff(c_44, plain, (![A_46, B_47]: (m1_subset_1(k2_tops_1(A_46, B_47), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_126])).
% 19.31/10.95  tff(c_20804, plain, (![A_447, B_448]: (k4_subset_1(u1_struct_0(A_447), B_448, k2_tops_1(A_447, B_448))=k2_pre_topc(A_447, B_448) | ~m1_subset_1(B_448, k1_zfmisc_1(u1_struct_0(A_447))) | ~l1_pre_topc(A_447))), inference(cnfTransformation, [status(thm)], [f_140])).
% 19.31/10.95  tff(c_20827, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_20804])).
% 19.31/10.95  tff(c_20849, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_20827])).
% 19.31/10.95  tff(c_441, plain, (![A_89, B_90, C_91]: (r1_tarski(k4_subset_1(A_89, B_90, C_91), A_89) | ~m1_subset_1(C_91, k1_zfmisc_1(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(resolution, [status(thm)], [c_407, c_38])).
% 19.31/10.95  tff(c_20853, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_20849, c_441])).
% 19.31/10.95  tff(c_20860, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20853])).
% 19.31/10.95  tff(c_20864, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_20860])).
% 19.31/10.95  tff(c_20867, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_20864])).
% 19.31/10.95  tff(c_20874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_20867])).
% 19.31/10.95  tff(c_20876, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_20860])).
% 19.31/10.95  tff(c_111, plain, (![A_64, B_65]: (m1_subset_1(k3_subset_1(A_64, B_65), k1_zfmisc_1(A_64)) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.31/10.95  tff(c_115, plain, (![A_64, B_65]: (r1_tarski(k3_subset_1(A_64, B_65), A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(resolution, [status(thm)], [c_111, c_38])).
% 19.31/10.95  tff(c_120, plain, (![A_68, B_69]: (k3_subset_1(A_68, k3_subset_1(A_68, B_69))=B_69 | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.31/10.95  tff(c_129, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_52, c_120])).
% 19.31/10.95  tff(c_40, plain, (![A_41, B_42]: (m1_subset_1(A_41, k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_113])).
% 19.31/10.95  tff(c_191, plain, (![B_74, A_75]: (k4_subset_1(B_74, A_75, k3_subset_1(B_74, A_75))=k2_subset_1(B_74) | ~r1_tarski(A_75, B_74))), inference(resolution, [status(thm)], [c_40, c_142])).
% 19.31/10.95  tff(c_203, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_2')=k2_subset_1(u1_struct_0('#skF_1')) | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_191])).
% 19.31/10.95  tff(c_222, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_203])).
% 19.31/10.95  tff(c_225, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_115, c_222])).
% 19.31/10.95  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_225])).
% 19.31/10.95  tff(c_231, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_203])).
% 19.31/10.95  tff(c_554, plain, (![A_92, B_93]: (k2_tops_1(A_92, k3_subset_1(u1_struct_0(A_92), B_93))=k2_tops_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_133])).
% 19.31/10.95  tff(c_571, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_554])).
% 19.31/10.95  tff(c_584, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_571])).
% 19.31/10.95  tff(c_26078, plain, (![A_521, A_522]: (k4_subset_1(u1_struct_0(A_521), A_522, k2_tops_1(A_521, A_522))=k2_pre_topc(A_521, A_522) | ~l1_pre_topc(A_521) | ~r1_tarski(A_522, u1_struct_0(A_521)))), inference(resolution, [status(thm)], [c_40, c_20804])).
% 19.31/10.95  tff(c_26121, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_584, c_26078])).
% 19.31/10.95  tff(c_26143, plain, (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_54, c_26121])).
% 19.31/10.95  tff(c_12, plain, (![A_7, B_8, C_9]: (m1_subset_1(k4_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 19.31/10.95  tff(c_42324, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_26143, c_12])).
% 19.31/10.95  tff(c_42356, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_20876, c_42324])).
% 19.31/10.95  tff(c_22270, plain, (![A_467, B_468]: (k3_subset_1(u1_struct_0(A_467), k2_pre_topc(A_467, k3_subset_1(u1_struct_0(A_467), B_468)))=k1_tops_1(A_467, B_468) | ~m1_subset_1(B_468, k1_zfmisc_1(u1_struct_0(A_467))) | ~l1_pre_topc(A_467))), inference(cnfTransformation, [status(thm)], [f_120])).
% 19.31/10.95  tff(c_22329, plain, (![A_467, B_468]: (m1_subset_1(k1_tops_1(A_467, B_468), k1_zfmisc_1(u1_struct_0(A_467))) | ~m1_subset_1(k2_pre_topc(A_467, k3_subset_1(u1_struct_0(A_467), B_468)), k1_zfmisc_1(u1_struct_0(A_467))) | ~m1_subset_1(B_468, k1_zfmisc_1(u1_struct_0(A_467))) | ~l1_pre_topc(A_467))), inference(superposition, [status(thm), theory('equality')], [c_22270, c_10])).
% 19.31/10.95  tff(c_42500, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42356, c_22329])).
% 19.31/10.95  tff(c_42551, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_42500])).
% 19.31/10.95  tff(c_20989, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20876, c_38])).
% 19.31/10.95  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.31/10.95  tff(c_331, plain, (![A_84, B_85, C_86]: (k4_subset_1(A_84, B_85, C_86)=k2_xboole_0(B_85, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 19.31/10.95  tff(c_20469, plain, (![B_431, B_432, A_433]: (k4_subset_1(B_431, B_432, A_433)=k2_xboole_0(B_432, A_433) | ~m1_subset_1(B_432, k1_zfmisc_1(B_431)) | ~r1_tarski(A_433, B_431))), inference(resolution, [status(thm)], [c_40, c_331])).
% 19.31/10.95  tff(c_51232, plain, (![A_807, B_808, A_809]: (k4_subset_1(A_807, k3_subset_1(A_807, B_808), A_809)=k2_xboole_0(k3_subset_1(A_807, B_808), A_809) | ~r1_tarski(A_809, A_807) | ~m1_subset_1(B_808, k1_zfmisc_1(A_807)))), inference(resolution, [status(thm)], [c_10, c_20469])).
% 19.31/10.95  tff(c_51453, plain, (![A_811]: (k4_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_811)=k2_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_811) | ~r1_tarski(A_811, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_51232])).
% 19.31/10.95  tff(c_51466, plain, (k2_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51453, c_26143])).
% 19.31/10.95  tff(c_51585, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20989, c_2, c_51466])).
% 19.31/10.95  tff(c_27364, plain, (![A_538, B_539, B_540]: (k4_subset_1(A_538, B_539, k3_subset_1(A_538, B_540))=k2_xboole_0(B_539, k3_subset_1(A_538, B_540)) | ~m1_subset_1(B_539, k1_zfmisc_1(A_538)) | ~m1_subset_1(B_540, k1_zfmisc_1(A_538)))), inference(resolution, [status(thm)], [c_10, c_331])).
% 19.31/10.95  tff(c_51661, plain, (![B_812, A_813, B_814]: (k4_subset_1(B_812, A_813, k3_subset_1(B_812, B_814))=k2_xboole_0(A_813, k3_subset_1(B_812, B_814)) | ~m1_subset_1(B_814, k1_zfmisc_1(B_812)) | ~r1_tarski(A_813, B_812))), inference(resolution, [status(thm)], [c_40, c_27364])).
% 19.31/10.95  tff(c_51927, plain, (![A_816]: (k4_subset_1(u1_struct_0('#skF_1'), A_816, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_xboole_0(A_816, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~r1_tarski(A_816, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_51661])).
% 19.31/10.95  tff(c_28, plain, (![A_29, B_30, C_32]: (r1_tarski(k3_subset_1(A_29, k4_subset_1(A_29, B_30, C_32)), k3_subset_1(A_29, B_30)) | ~m1_subset_1(C_32, k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 19.31/10.95  tff(c_22060, plain, (![B_464, C_465, A_466]: (r1_tarski(B_464, C_465) | ~r1_tarski(k3_subset_1(A_466, C_465), k3_subset_1(A_466, B_464)) | ~m1_subset_1(C_465, k1_zfmisc_1(A_466)) | ~m1_subset_1(B_464, k1_zfmisc_1(A_466)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.31/10.95  tff(c_29344, plain, (![B_569, A_570, C_571]: (r1_tarski(B_569, k4_subset_1(A_570, B_569, C_571)) | ~m1_subset_1(k4_subset_1(A_570, B_569, C_571), k1_zfmisc_1(A_570)) | ~m1_subset_1(C_571, k1_zfmisc_1(A_570)) | ~m1_subset_1(B_569, k1_zfmisc_1(A_570)))), inference(resolution, [status(thm)], [c_28, c_22060])).
% 19.31/10.95  tff(c_29490, plain, (![B_8, A_7, C_9]: (r1_tarski(B_8, k4_subset_1(A_7, B_8, C_9)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_12, c_29344])).
% 19.31/10.95  tff(c_51975, plain, (![A_816]: (r1_tarski(A_816, k2_xboole_0(A_816, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(A_816, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_816, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_51927, c_29490])).
% 19.31/10.95  tff(c_53757, plain, (![A_830]: (r1_tarski(A_830, k2_xboole_0(A_830, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(A_830, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_830, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_51975])).
% 19.31/10.95  tff(c_53782, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51585, c_53757])).
% 19.31/10.95  tff(c_53812, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20989, c_20876, c_53782])).
% 19.31/10.95  tff(c_22, plain, (![A_17, C_20, B_18]: (r1_tarski(k3_subset_1(A_17, C_20), k3_subset_1(A_17, B_18)) | ~r1_tarski(B_18, C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.31/10.95  tff(c_22287, plain, (![A_467, B_468, B_18]: (r1_tarski(k1_tops_1(A_467, B_468), k3_subset_1(u1_struct_0(A_467), B_18)) | ~r1_tarski(B_18, k2_pre_topc(A_467, k3_subset_1(u1_struct_0(A_467), B_468))) | ~m1_subset_1(k2_pre_topc(A_467, k3_subset_1(u1_struct_0(A_467), B_468)), k1_zfmisc_1(u1_struct_0(A_467))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_467))) | ~m1_subset_1(B_468, k1_zfmisc_1(u1_struct_0(A_467))) | ~l1_pre_topc(A_467))), inference(superposition, [status(thm), theory('equality')], [c_22270, c_22])).
% 19.31/10.95  tff(c_53844, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_53812, c_22287])).
% 19.31/10.95  tff(c_53855, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_20876, c_42356, c_53844])).
% 19.31/10.95  tff(c_30, plain, (![B_34, C_36, A_33]: (r1_xboole_0(B_34, C_36) | ~r1_tarski(B_34, k3_subset_1(A_33, C_36)) | ~m1_subset_1(C_36, k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 19.31/10.95  tff(c_54537, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_53855, c_30])).
% 19.31/10.95  tff(c_54550, plain, (r1_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42551, c_20876, c_54537])).
% 19.31/10.95  tff(c_54552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_54550])).
% 19.31/10.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.31/10.95  
% 19.31/10.95  Inference rules
% 19.31/10.95  ----------------------
% 19.31/10.95  #Ref     : 0
% 19.31/10.95  #Sup     : 12848
% 19.31/10.95  #Fact    : 0
% 19.31/10.95  #Define  : 0
% 19.31/10.95  #Split   : 112
% 19.31/10.95  #Chain   : 0
% 19.31/10.95  #Close   : 0
% 19.31/10.95  
% 19.31/10.95  Ordering : KBO
% 19.31/10.95  
% 19.31/10.95  Simplification rules
% 19.31/10.95  ----------------------
% 19.31/10.95  #Subsume      : 848
% 19.31/10.95  #Demod        : 15306
% 19.31/10.95  #Tautology    : 3788
% 19.31/10.95  #SimpNegUnit  : 148
% 19.31/10.95  #BackRed      : 145
% 19.31/10.95  
% 19.31/10.95  #Partial instantiations: 0
% 19.31/10.95  #Strategies tried      : 1
% 19.31/10.95  
% 19.31/10.95  Timing (in seconds)
% 19.31/10.95  ----------------------
% 19.31/10.96  Preprocessing        : 0.48
% 19.31/10.96  Parsing              : 0.25
% 19.31/10.96  CNF conversion       : 0.05
% 19.31/10.96  Main loop            : 9.69
% 19.31/10.96  Inferencing          : 1.73
% 19.31/10.96  Reduction            : 4.85
% 19.31/10.96  Demodulation         : 4.02
% 19.31/10.96  BG Simplification    : 0.22
% 19.31/10.96  Subsumption          : 2.36
% 19.31/10.96  Abstraction          : 0.32
% 19.31/10.96  MUC search           : 0.00
% 19.31/10.96  Cooper               : 0.00
% 19.31/10.96  Total                : 10.21
% 19.31/10.96  Index Insertion      : 0.00
% 19.31/10.96  Index Deletion       : 0.00
% 19.31/10.96  Index Matching       : 0.00
% 19.31/10.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
