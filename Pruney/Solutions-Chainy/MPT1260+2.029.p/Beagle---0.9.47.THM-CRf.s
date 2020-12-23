%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:04 EST 2020

% Result     : Theorem 22.77s
% Output     : CNFRefutation 22.77s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 286 expanded)
%              Number of leaves         :   39 ( 112 expanded)
%              Depth                    :   10
%              Number of atoms          :  189 ( 609 expanded)
%              Number of equality atoms :   62 ( 178 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_120,axiom,(
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

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_74,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_142,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_237,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1656,plain,(
    ! [A_136,B_137,C_138] :
      ( k7_subset_1(A_136,B_137,C_138) = k4_xboole_0(B_137,C_138)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1665,plain,(
    ! [C_138] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_138) = k4_xboole_0('#skF_2',C_138) ),
    inference(resolution,[status(thm)],[c_62,c_1656])).

tff(c_5038,plain,(
    ! [A_188,B_189] :
      ( k7_subset_1(u1_struct_0(A_188),B_189,k2_tops_1(A_188,B_189)) = k1_tops_1(A_188,B_189)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_5051,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_5038])).

tff(c_5058,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1665,c_5051])).

tff(c_26,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5092,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5058,c_26])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_306,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | ~ r1_tarski(B_91,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7360,plain,(
    ! [A_213,B_214] :
      ( k4_xboole_0(A_213,B_214) = A_213
      | ~ r1_tarski(A_213,k4_xboole_0(A_213,B_214)) ) ),
    inference(resolution,[status(thm)],[c_22,c_306])).

tff(c_7366,plain,
    ( k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5058,c_7360])).

tff(c_7436,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5058,c_7366])).

tff(c_39875,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7436])).

tff(c_39879,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_39875])).

tff(c_48917,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5092,c_39879])).

tff(c_46,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12388,plain,(
    ! [B_272,A_273,C_274] :
      ( k7_subset_1(B_272,A_273,C_274) = k4_xboole_0(A_273,C_274)
      | ~ r1_tarski(A_273,B_272) ) ),
    inference(resolution,[status(thm)],[c_46,c_1656])).

tff(c_59982,plain,(
    ! [B_605,A_606,C_607] :
      ( k7_subset_1(B_605,A_606,C_607) = k4_xboole_0(A_606,C_607)
      | k4_xboole_0(A_606,B_605) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_12388])).

tff(c_60036,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_59982,c_142])).

tff(c_65233,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60036])).

tff(c_48,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k2_tops_1(A_42,B_43),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5467,plain,(
    ! [A_190,B_191] :
      ( k4_subset_1(u1_struct_0(A_190),B_191,k2_tops_1(A_190,B_191)) = k2_pre_topc(A_190,B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_5480,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_5467])).

tff(c_5487,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5480])).

tff(c_3839,plain,(
    ! [A_173,B_174,C_175] :
      ( m1_subset_1(k4_subset_1(A_173,B_174,C_175),k1_zfmisc_1(A_173))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(A_173))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_15312,plain,(
    ! [A_297,B_298,C_299] :
      ( r1_tarski(k4_subset_1(A_297,B_298,C_299),A_297)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(A_297))
      | ~ m1_subset_1(B_298,k1_zfmisc_1(A_297)) ) ),
    inference(resolution,[status(thm)],[c_3839,c_44])).

tff(c_15339,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5487,c_15312])).

tff(c_15350,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_15339])).

tff(c_92411,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15350])).

tff(c_92414,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_92411])).

tff(c_92421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_92414])).

tff(c_92422,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_15350])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92436,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92422,c_12])).

tff(c_92447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65233,c_92436])).

tff(c_92449,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60036])).

tff(c_60081,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_59982])).

tff(c_92719,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92449,c_60081])).

tff(c_917,plain,(
    ! [A_121,B_122,C_123] : k4_xboole_0(k3_xboole_0(A_121,B_122),C_123) = k3_xboole_0(A_121,k4_xboole_0(B_122,C_123)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_577,plain,(
    ! [A_105,B_106] : k4_xboole_0(A_105,k4_xboole_0(A_105,B_106)) = k3_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_182,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = k1_xboole_0
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,(
    ! [A_15,B_16] : k4_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_182])).

tff(c_586,plain,(
    ! [A_105,B_106] : k4_xboole_0(k3_xboole_0(A_105,B_106),A_105) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_197])).

tff(c_928,plain,(
    ! [C_123,B_122] : k3_xboole_0(C_123,k4_xboole_0(B_122,C_123)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_586])).

tff(c_92892,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92719,c_928])).

tff(c_92925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48917,c_92892])).

tff(c_92926,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7436])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_3128,plain,(
    ! [A_161,B_162] :
      ( v3_pre_topc(k1_tops_1(A_161,B_162),A_161)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3136,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_3128])).

tff(c_3141,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3136])).

tff(c_92950,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92926,c_3141])).

tff(c_92970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_92950])).

tff(c_92971,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_93350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_92971])).

tff(c_93351,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_93424,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93351,c_68])).

tff(c_94863,plain,(
    ! [A_807,B_808,C_809] :
      ( k7_subset_1(A_807,B_808,C_809) = k4_xboole_0(B_808,C_809)
      | ~ m1_subset_1(B_808,k1_zfmisc_1(A_807)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_94872,plain,(
    ! [C_809] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_809) = k4_xboole_0('#skF_2',C_809) ),
    inference(resolution,[status(thm)],[c_62,c_94863])).

tff(c_99032,plain,(
    ! [A_868,B_869] :
      ( k7_subset_1(u1_struct_0(A_868),B_869,k2_tops_1(A_868,B_869)) = k1_tops_1(A_868,B_869)
      | ~ m1_subset_1(B_869,k1_zfmisc_1(u1_struct_0(A_868)))
      | ~ l1_pre_topc(A_868) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_99045,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_99032])).

tff(c_99052,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_94872,c_99045])).

tff(c_99098,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_99052,c_22])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99911,plain,(
    ! [B_875,A_876,C_877] :
      ( r1_tarski(B_875,k1_tops_1(A_876,C_877))
      | ~ r1_tarski(B_875,C_877)
      | ~ v3_pre_topc(B_875,A_876)
      | ~ m1_subset_1(C_877,k1_zfmisc_1(u1_struct_0(A_876)))
      | ~ m1_subset_1(B_875,k1_zfmisc_1(u1_struct_0(A_876)))
      | ~ l1_pre_topc(A_876) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_99924,plain,(
    ! [B_875] :
      ( r1_tarski(B_875,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_875,'#skF_2')
      | ~ v3_pre_topc(B_875,'#skF_1')
      | ~ m1_subset_1(B_875,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_99911])).

tff(c_100329,plain,(
    ! [B_883] :
      ( r1_tarski(B_883,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_883,'#skF_2')
      | ~ v3_pre_topc(B_883,'#skF_1')
      | ~ m1_subset_1(B_883,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99924])).

tff(c_100348,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_100329])).

tff(c_100357,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93351,c_8,c_100348])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100359,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_100357,c_4])).

tff(c_100368,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99098,c_100359])).

tff(c_52,plain,(
    ! [A_46,B_48] :
      ( k7_subset_1(u1_struct_0(A_46),k2_pre_topc(A_46,B_48),k1_tops_1(A_46,B_48)) = k2_tops_1(A_46,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_100390,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_100368,c_52])).

tff(c_100394,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_100390])).

tff(c_100396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93424,c_100394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:06:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.77/14.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.77/14.20  
% 22.77/14.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.77/14.21  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 22.77/14.21  
% 22.77/14.21  %Foreground sorts:
% 22.77/14.21  
% 22.77/14.21  
% 22.77/14.21  %Background operators:
% 22.77/14.21  
% 22.77/14.21  
% 22.77/14.21  %Foreground operators:
% 22.77/14.21  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 22.77/14.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.77/14.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.77/14.21  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 22.77/14.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.77/14.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 22.77/14.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 22.77/14.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.77/14.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.77/14.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 22.77/14.21  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 22.77/14.21  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 22.77/14.21  tff('#skF_2', type, '#skF_2': $i).
% 22.77/14.21  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 22.77/14.21  tff('#skF_1', type, '#skF_1': $i).
% 22.77/14.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.77/14.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.77/14.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.77/14.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 22.77/14.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.77/14.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 22.77/14.21  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 22.77/14.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.77/14.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 22.77/14.21  
% 22.77/14.23  tff(f_153, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 22.77/14.23  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 22.77/14.23  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 22.77/14.23  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 22.77/14.23  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 22.77/14.23  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 22.77/14.23  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.77/14.23  tff(f_85, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 22.77/14.23  tff(f_91, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 22.77/14.23  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 22.77/14.23  tff(f_71, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 22.77/14.23  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 22.77/14.23  tff(f_99, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 22.77/14.23  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 22.77/14.23  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 22.77/14.23  tff(c_74, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 22.77/14.23  tff(c_142, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_74])).
% 22.77/14.23  tff(c_68, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 22.77/14.23  tff(c_237, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_68])).
% 22.77/14.23  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 22.77/14.23  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 22.77/14.23  tff(c_1656, plain, (![A_136, B_137, C_138]: (k7_subset_1(A_136, B_137, C_138)=k4_xboole_0(B_137, C_138) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 22.77/14.23  tff(c_1665, plain, (![C_138]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_138)=k4_xboole_0('#skF_2', C_138))), inference(resolution, [status(thm)], [c_62, c_1656])).
% 22.77/14.23  tff(c_5038, plain, (![A_188, B_189]: (k7_subset_1(u1_struct_0(A_188), B_189, k2_tops_1(A_188, B_189))=k1_tops_1(A_188, B_189) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_141])).
% 22.77/14.23  tff(c_5051, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_5038])).
% 22.77/14.23  tff(c_5058, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1665, c_5051])).
% 22.77/14.23  tff(c_26, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.77/14.23  tff(c_5092, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5058, c_26])).
% 22.77/14.23  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.77/14.23  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.77/14.23  tff(c_306, plain, (![B_91, A_92]: (B_91=A_92 | ~r1_tarski(B_91, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.77/14.23  tff(c_7360, plain, (![A_213, B_214]: (k4_xboole_0(A_213, B_214)=A_213 | ~r1_tarski(A_213, k4_xboole_0(A_213, B_214)))), inference(resolution, [status(thm)], [c_22, c_306])).
% 22.77/14.23  tff(c_7366, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5058, c_7360])).
% 22.77/14.23  tff(c_7436, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5058, c_7366])).
% 22.77/14.23  tff(c_39875, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_7436])).
% 22.77/14.23  tff(c_39879, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_39875])).
% 22.77/14.23  tff(c_48917, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5092, c_39879])).
% 22.77/14.23  tff(c_46, plain, (![A_40, B_41]: (m1_subset_1(A_40, k1_zfmisc_1(B_41)) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.77/14.23  tff(c_12388, plain, (![B_272, A_273, C_274]: (k7_subset_1(B_272, A_273, C_274)=k4_xboole_0(A_273, C_274) | ~r1_tarski(A_273, B_272))), inference(resolution, [status(thm)], [c_46, c_1656])).
% 22.77/14.23  tff(c_59982, plain, (![B_605, A_606, C_607]: (k7_subset_1(B_605, A_606, C_607)=k4_xboole_0(A_606, C_607) | k4_xboole_0(A_606, B_605)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_12388])).
% 22.77/14.23  tff(c_60036, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_59982, c_142])).
% 22.77/14.23  tff(c_65233, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60036])).
% 22.77/14.23  tff(c_48, plain, (![A_42, B_43]: (m1_subset_1(k2_tops_1(A_42, B_43), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_91])).
% 22.77/14.23  tff(c_5467, plain, (![A_190, B_191]: (k4_subset_1(u1_struct_0(A_190), B_191, k2_tops_1(A_190, B_191))=k2_pre_topc(A_190, B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_134])).
% 22.77/14.23  tff(c_5480, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_5467])).
% 22.77/14.23  tff(c_5487, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5480])).
% 22.77/14.23  tff(c_3839, plain, (![A_173, B_174, C_175]: (m1_subset_1(k4_subset_1(A_173, B_174, C_175), k1_zfmisc_1(A_173)) | ~m1_subset_1(C_175, k1_zfmisc_1(A_173)) | ~m1_subset_1(B_174, k1_zfmisc_1(A_173)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 22.77/14.23  tff(c_44, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 22.77/14.23  tff(c_15312, plain, (![A_297, B_298, C_299]: (r1_tarski(k4_subset_1(A_297, B_298, C_299), A_297) | ~m1_subset_1(C_299, k1_zfmisc_1(A_297)) | ~m1_subset_1(B_298, k1_zfmisc_1(A_297)))), inference(resolution, [status(thm)], [c_3839, c_44])).
% 22.77/14.23  tff(c_15339, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_5487, c_15312])).
% 22.77/14.23  tff(c_15350, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_15339])).
% 22.77/14.23  tff(c_92411, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_15350])).
% 22.77/14.23  tff(c_92414, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_92411])).
% 22.77/14.23  tff(c_92421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_92414])).
% 22.77/14.23  tff(c_92422, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_15350])).
% 22.77/14.23  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.77/14.23  tff(c_92436, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_92422, c_12])).
% 22.77/14.23  tff(c_92447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65233, c_92436])).
% 22.77/14.23  tff(c_92449, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_60036])).
% 22.77/14.23  tff(c_60081, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_142, c_59982])).
% 22.77/14.23  tff(c_92719, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92449, c_60081])).
% 22.77/14.23  tff(c_917, plain, (![A_121, B_122, C_123]: (k4_xboole_0(k3_xboole_0(A_121, B_122), C_123)=k3_xboole_0(A_121, k4_xboole_0(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 22.77/14.23  tff(c_577, plain, (![A_105, B_106]: (k4_xboole_0(A_105, k4_xboole_0(A_105, B_106))=k3_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.77/14.23  tff(c_182, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=k1_xboole_0 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.77/14.23  tff(c_197, plain, (![A_15, B_16]: (k4_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_182])).
% 22.77/14.23  tff(c_586, plain, (![A_105, B_106]: (k4_xboole_0(k3_xboole_0(A_105, B_106), A_105)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_577, c_197])).
% 22.77/14.23  tff(c_928, plain, (![C_123, B_122]: (k3_xboole_0(C_123, k4_xboole_0(B_122, C_123))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_917, c_586])).
% 22.77/14.23  tff(c_92892, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92719, c_928])).
% 22.77/14.23  tff(c_92925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48917, c_92892])).
% 22.77/14.23  tff(c_92926, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_7436])).
% 22.77/14.23  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 22.77/14.23  tff(c_3128, plain, (![A_161, B_162]: (v3_pre_topc(k1_tops_1(A_161, B_162), A_161) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.77/14.23  tff(c_3136, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_3128])).
% 22.77/14.23  tff(c_3141, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3136])).
% 22.77/14.23  tff(c_92950, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92926, c_3141])).
% 22.77/14.23  tff(c_92970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_92950])).
% 22.77/14.23  tff(c_92971, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_68])).
% 22.77/14.23  tff(c_93350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_92971])).
% 22.77/14.23  tff(c_93351, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_74])).
% 22.77/14.23  tff(c_93424, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93351, c_68])).
% 22.77/14.23  tff(c_94863, plain, (![A_807, B_808, C_809]: (k7_subset_1(A_807, B_808, C_809)=k4_xboole_0(B_808, C_809) | ~m1_subset_1(B_808, k1_zfmisc_1(A_807)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 22.77/14.23  tff(c_94872, plain, (![C_809]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_809)=k4_xboole_0('#skF_2', C_809))), inference(resolution, [status(thm)], [c_62, c_94863])).
% 22.77/14.23  tff(c_99032, plain, (![A_868, B_869]: (k7_subset_1(u1_struct_0(A_868), B_869, k2_tops_1(A_868, B_869))=k1_tops_1(A_868, B_869) | ~m1_subset_1(B_869, k1_zfmisc_1(u1_struct_0(A_868))) | ~l1_pre_topc(A_868))), inference(cnfTransformation, [status(thm)], [f_141])).
% 22.77/14.23  tff(c_99045, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_99032])).
% 22.77/14.23  tff(c_99052, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_94872, c_99045])).
% 22.77/14.23  tff(c_99098, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_99052, c_22])).
% 22.77/14.23  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.77/14.23  tff(c_99911, plain, (![B_875, A_876, C_877]: (r1_tarski(B_875, k1_tops_1(A_876, C_877)) | ~r1_tarski(B_875, C_877) | ~v3_pre_topc(B_875, A_876) | ~m1_subset_1(C_877, k1_zfmisc_1(u1_struct_0(A_876))) | ~m1_subset_1(B_875, k1_zfmisc_1(u1_struct_0(A_876))) | ~l1_pre_topc(A_876))), inference(cnfTransformation, [status(thm)], [f_120])).
% 22.77/14.23  tff(c_99924, plain, (![B_875]: (r1_tarski(B_875, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_875, '#skF_2') | ~v3_pre_topc(B_875, '#skF_1') | ~m1_subset_1(B_875, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_99911])).
% 22.77/14.23  tff(c_100329, plain, (![B_883]: (r1_tarski(B_883, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_883, '#skF_2') | ~v3_pre_topc(B_883, '#skF_1') | ~m1_subset_1(B_883, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99924])).
% 22.77/14.23  tff(c_100348, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_100329])).
% 22.77/14.23  tff(c_100357, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_93351, c_8, c_100348])).
% 22.77/14.23  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.77/14.23  tff(c_100359, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_100357, c_4])).
% 22.77/14.23  tff(c_100368, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_99098, c_100359])).
% 22.77/14.23  tff(c_52, plain, (![A_46, B_48]: (k7_subset_1(u1_struct_0(A_46), k2_pre_topc(A_46, B_48), k1_tops_1(A_46, B_48))=k2_tops_1(A_46, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_106])).
% 22.77/14.23  tff(c_100390, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_100368, c_52])).
% 22.77/14.23  tff(c_100394, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_100390])).
% 22.77/14.23  tff(c_100396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93424, c_100394])).
% 22.77/14.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.77/14.23  
% 22.77/14.23  Inference rules
% 22.77/14.23  ----------------------
% 22.77/14.23  #Ref     : 0
% 22.77/14.23  #Sup     : 25093
% 22.77/14.23  #Fact    : 0
% 22.77/14.23  #Define  : 0
% 22.77/14.23  #Split   : 11
% 22.77/14.23  #Chain   : 0
% 22.77/14.23  #Close   : 0
% 22.77/14.23  
% 22.77/14.23  Ordering : KBO
% 22.77/14.23  
% 22.77/14.23  Simplification rules
% 22.77/14.23  ----------------------
% 22.77/14.23  #Subsume      : 728
% 22.77/14.23  #Demod        : 30740
% 22.77/14.23  #Tautology    : 16999
% 22.77/14.23  #SimpNegUnit  : 70
% 22.77/14.23  #BackRed      : 42
% 22.77/14.23  
% 22.77/14.23  #Partial instantiations: 0
% 22.77/14.23  #Strategies tried      : 1
% 22.77/14.23  
% 22.77/14.23  Timing (in seconds)
% 22.77/14.23  ----------------------
% 22.77/14.23  Preprocessing        : 0.36
% 22.77/14.23  Parsing              : 0.19
% 22.77/14.23  CNF conversion       : 0.02
% 22.77/14.23  Main loop            : 13.09
% 22.77/14.23  Inferencing          : 1.51
% 22.77/14.23  Reduction            : 8.21
% 22.77/14.23  Demodulation         : 7.36
% 22.77/14.23  BG Simplification    : 0.17
% 22.77/14.23  Subsumption          : 2.68
% 22.77/14.23  Abstraction          : 0.33
% 22.77/14.23  MUC search           : 0.00
% 22.77/14.23  Cooper               : 0.00
% 22.77/14.23  Total                : 13.50
% 22.77/14.23  Index Insertion      : 0.00
% 22.77/14.23  Index Deletion       : 0.00
% 22.77/14.23  Index Matching       : 0.00
% 22.77/14.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
