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
% DateTime   : Thu Dec  3 10:20:51 EST 2020

% Result     : Theorem 10.76s
% Output     : CNFRefutation 10.76s
% Verified   : 
% Statistics : Number of formulae       :  120 (1427 expanded)
%              Number of leaves         :   29 ( 471 expanded)
%              Depth                    :   21
%              Number of atoms          :  230 (3246 expanded)
%              Number of equality atoms :   36 ( 428 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(k2_tops_1(A,k2_tops_1(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(c_32,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_tops_1(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_153,plain,(
    ! [A_58,B_59] :
      ( k4_subset_1(u1_struct_0(A_58),B_59,k2_tops_1(A_58,B_59)) = k2_pre_topc(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_162,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_153])).

tff(c_168,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_162])).

tff(c_238,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(k3_subset_1(A_63,k4_subset_1(A_63,B_64,C_65)),k3_subset_1(A_63,B_64))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_252,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_238])).

tff(c_264,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_252])).

tff(c_296,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_319,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_296])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_319])).

tff(c_325,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_pre_topc(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_74,plain,(
    ! [A_50,B_51,C_52] :
      ( k4_subset_1(A_50,B_51,C_52) = k2_xboole_0(B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2444,plain,(
    ! [A_137,B_138,B_139] :
      ( k4_subset_1(u1_struct_0(A_137),B_138,k2_tops_1(A_137,B_139)) = k2_xboole_0(B_138,k2_tops_1(A_137,B_139))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_28,c_74])).

tff(c_2457,plain,(
    ! [B_139] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_139)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_139))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_2444])).

tff(c_2470,plain,(
    ! [B_140] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_140)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_140))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2457])).

tff(c_2493,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_325,c_2470])).

tff(c_18,plain,(
    ! [A_15,B_16,C_18] :
      ( r1_tarski(k3_subset_1(A_15,k4_subset_1(A_15,B_16,C_18)),k3_subset_1(A_15,B_16))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2509,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2493,c_18])).

tff(c_2515,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0('#skF_2',k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2509])).

tff(c_4433,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2515])).

tff(c_4436,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_4433])).

tff(c_4440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_325,c_4436])).

tff(c_4442,plain,(
    m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2515])).

tff(c_30,plain,(
    ! [A_35,B_37] :
      ( k4_subset_1(u1_struct_0(A_35),B_37,k2_tops_1(A_35,B_37)) = k2_pre_topc(A_35,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_333,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_325,c_30])).

tff(c_350,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_333])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( k4_subset_1(A_3,C_5,B_4) = k4_subset_1(A_3,B_4,C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_353,plain,(
    ! [B_4] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),B_4) = k4_subset_1(u1_struct_0('#skF_1'),B_4,k2_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_325,c_8])).

tff(c_4464,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) = k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4442,c_353])).

tff(c_4524,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_4464])).

tff(c_270,plain,(
    ! [B_66,C_67,A_68] :
      ( r1_tarski(B_66,C_67)
      | ~ r1_tarski(k3_subset_1(A_68,C_67),k3_subset_1(A_68,B_66))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_284,plain,(
    ! [B_16,A_15,C_18] :
      ( r1_tarski(B_16,k4_subset_1(A_15,B_16,C_18))
      | ~ m1_subset_1(k4_subset_1(A_15,B_16,C_18),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_18,c_270])).

tff(c_4657,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4524,c_284])).

tff(c_4676,plain,
    ( r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4442,c_325,c_4524,c_4657])).

tff(c_5418,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4676])).

tff(c_5421,plain,
    ( ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_5418])).

tff(c_5425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_325,c_5421])).

tff(c_5427,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_4676])).

tff(c_2448,plain,(
    ! [B_139] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',B_139)) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',B_139))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_325,c_2444])).

tff(c_2708,plain,(
    ! [B_146] :
      ( k4_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',B_146)) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',B_146))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2448])).

tff(c_164,plain,(
    ! [A_33,B_34] :
      ( k4_subset_1(u1_struct_0(A_33),k2_tops_1(A_33,B_34),k2_tops_1(A_33,k2_tops_1(A_33,B_34))) = k2_pre_topc(A_33,k2_tops_1(A_33,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_28,c_153])).

tff(c_2715,plain,
    ( k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2708,c_164])).

tff(c_2750,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_36,c_34,c_2715])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( k4_subset_1(A_8,B_9,C_10) = k2_xboole_0(B_9,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7716,plain,(
    ! [B_215] :
      ( k4_subset_1(u1_struct_0('#skF_1'),B_215,k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2'))) = k2_xboole_0(B_215,k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_4442,c_12])).

tff(c_7764,plain,(
    ! [B_215] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0(B_215,k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))),k3_subset_1(u1_struct_0('#skF_1'),B_215))
      | ~ m1_subset_1(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7716,c_18])).

tff(c_7865,plain,(
    ! [B_216] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_xboole_0(B_216,k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')))),k3_subset_1(u1_struct_0('#skF_1'),B_216))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4442,c_7764])).

tff(c_7878,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2750,c_7865])).

tff(c_7884,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_7878])).

tff(c_14,plain,(
    ! [B_12,C_14,A_11] :
      ( r1_tarski(B_12,C_14)
      | ~ r1_tarski(k3_subset_1(A_11,C_14),k3_subset_1(A_11,B_12))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_7922,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_7884,c_14])).

tff(c_7931,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_5427,c_7922])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7938,plain,
    ( k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7931,c_2])).

tff(c_7939,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7938])).

tff(c_26,plain,(
    ! [A_30,B_32] :
      ( k9_subset_1(u1_struct_0(A_30),k2_pre_topc(A_30,B_32),k2_pre_topc(A_30,k3_subset_1(u1_struct_0(A_30),B_32))) = k2_tops_1(A_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_48,B_49] :
      ( k2_pre_topc(A_48,k2_pre_topc(A_48,B_49)) = k2_pre_topc(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_61,plain,(
    ! [A_48,B_7] :
      ( k2_pre_topc(A_48,k2_pre_topc(A_48,k3_subset_1(u1_struct_0(A_48),B_7))) = k2_pre_topc(A_48,k3_subset_1(u1_struct_0(A_48),B_7))
      | ~ l1_pre_topc(A_48)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_48))) ) ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_324,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_376,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_324,c_14])).

tff(c_381,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_376])).

tff(c_411,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_414,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_411])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_414])).

tff(c_420,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_58,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_64,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58])).

tff(c_489,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(k2_pre_topc(A_76,k9_subset_1(u1_struct_0(A_76),B_77,C_78)),k9_subset_1(u1_struct_0(A_76),k2_pre_topc(A_76,B_77),k2_pre_topc(A_76,C_78)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4784,plain,(
    ! [A_188,B_189] :
      ( r1_tarski(k2_pre_topc(A_188,k2_tops_1(A_188,B_189)),k9_subset_1(u1_struct_0(A_188),k2_pre_topc(A_188,k2_pre_topc(A_188,B_189)),k2_pre_topc(A_188,k2_pre_topc(A_188,k3_subset_1(u1_struct_0(A_188),B_189)))))
      | ~ m1_subset_1(k2_pre_topc(A_188,k3_subset_1(u1_struct_0(A_188),B_189)),k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(k2_pre_topc(A_188,B_189),k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_489])).

tff(c_4845,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4784])).

tff(c_4863,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_36,c_420,c_4845])).

tff(c_11625,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4863])).

tff(c_11628,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_11625])).

tff(c_11631,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_11628])).

tff(c_11634,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10,c_11631])).

tff(c_11638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_11634])).

tff(c_11639,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))))) ),
    inference(splitRight,[status(thm)],[c_4863])).

tff(c_12847,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_11639])).

tff(c_12851,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_12847])).

tff(c_12888,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_12851])).

tff(c_12892,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_12888])).

tff(c_12894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7939,c_12892])).

tff(c_12895,plain,(
    k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_7938])).

tff(c_5426,plain,(
    r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_pre_topc('#skF_1',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_4676])).

tff(c_12914,plain,(
    r1_tarski(k2_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12895,c_5426])).

tff(c_12940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_12914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.76/3.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.76/3.99  
% 10.76/3.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.76/3.99  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 10.76/3.99  
% 10.76/3.99  %Foreground sorts:
% 10.76/3.99  
% 10.76/3.99  
% 10.76/3.99  %Background operators:
% 10.76/3.99  
% 10.76/3.99  
% 10.76/3.99  %Foreground operators:
% 10.76/3.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.76/3.99  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.76/3.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.76/3.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.76/3.99  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.76/3.99  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.76/3.99  tff('#skF_2', type, '#skF_2': $i).
% 10.76/3.99  tff('#skF_1', type, '#skF_1': $i).
% 10.76/3.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.76/3.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.76/3.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.76/3.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.76/3.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.76/3.99  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.76/3.99  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.76/3.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.76/3.99  
% 10.76/4.01  tff(f_113, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_tops_1(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tops_1)).
% 10.76/4.01  tff(f_98, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 10.76/4.01  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 10.76/4.01  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 10.76/4.01  tff(f_69, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.76/4.01  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.76/4.01  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 10.76/4.01  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 10.76/4.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.76/4.01  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 10.76/4.01  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.76/4.01  tff(f_75, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 10.76/4.01  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 10.76/4.01  tff(c_32, plain, (~r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.76/4.01  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.76/4.01  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.76/4.01  tff(c_28, plain, (![A_33, B_34]: (m1_subset_1(k2_tops_1(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.76/4.01  tff(c_153, plain, (![A_58, B_59]: (k4_subset_1(u1_struct_0(A_58), B_59, k2_tops_1(A_58, B_59))=k2_pre_topc(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.76/4.01  tff(c_162, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_153])).
% 10.76/4.01  tff(c_168, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_162])).
% 10.76/4.01  tff(c_238, plain, (![A_63, B_64, C_65]: (r1_tarski(k3_subset_1(A_63, k4_subset_1(A_63, B_64, C_65)), k3_subset_1(A_63, B_64)) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.76/4.01  tff(c_252, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_168, c_238])).
% 10.76/4.01  tff(c_264, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_252])).
% 10.76/4.01  tff(c_296, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_264])).
% 10.76/4.01  tff(c_319, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_296])).
% 10.76/4.01  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_319])).
% 10.76/4.01  tff(c_325, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_264])).
% 10.76/4.01  tff(c_20, plain, (![A_19, B_20]: (m1_subset_1(k2_pre_topc(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.76/4.01  tff(c_74, plain, (![A_50, B_51, C_52]: (k4_subset_1(A_50, B_51, C_52)=k2_xboole_0(B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.76/4.01  tff(c_2444, plain, (![A_137, B_138, B_139]: (k4_subset_1(u1_struct_0(A_137), B_138, k2_tops_1(A_137, B_139))=k2_xboole_0(B_138, k2_tops_1(A_137, B_139)) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_28, c_74])).
% 10.76/4.01  tff(c_2457, plain, (![B_139]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_139))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_139)) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_2444])).
% 10.76/4.01  tff(c_2470, plain, (![B_140]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_140))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_140)) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2457])).
% 10.76/4.01  tff(c_2493, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_325, c_2470])).
% 10.76/4.01  tff(c_18, plain, (![A_15, B_16, C_18]: (r1_tarski(k3_subset_1(A_15, k4_subset_1(A_15, B_16, C_18)), k3_subset_1(A_15, B_16)) | ~m1_subset_1(C_18, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.76/4.01  tff(c_2509, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2493, c_18])).
% 10.76/4.01  tff(c_2515, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0('#skF_2', k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2509])).
% 10.76/4.01  tff(c_4433, plain, (~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2515])).
% 10.76/4.01  tff(c_4436, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_4433])).
% 10.76/4.01  tff(c_4440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_325, c_4436])).
% 10.76/4.01  tff(c_4442, plain, (m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2515])).
% 10.76/4.01  tff(c_30, plain, (![A_35, B_37]: (k4_subset_1(u1_struct_0(A_35), B_37, k2_tops_1(A_35, B_37))=k2_pre_topc(A_35, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.76/4.01  tff(c_333, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_325, c_30])).
% 10.76/4.01  tff(c_350, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_333])).
% 10.76/4.01  tff(c_8, plain, (![A_3, C_5, B_4]: (k4_subset_1(A_3, C_5, B_4)=k4_subset_1(A_3, B_4, C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.76/4.01  tff(c_353, plain, (![B_4]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), B_4)=k4_subset_1(u1_struct_0('#skF_1'), B_4, k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_325, c_8])).
% 10.76/4.01  tff(c_4464, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))=k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_4442, c_353])).
% 10.76/4.01  tff(c_4524, plain, (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_4464])).
% 10.76/4.01  tff(c_270, plain, (![B_66, C_67, A_68]: (r1_tarski(B_66, C_67) | ~r1_tarski(k3_subset_1(A_68, C_67), k3_subset_1(A_68, B_66)) | ~m1_subset_1(C_67, k1_zfmisc_1(A_68)) | ~m1_subset_1(B_66, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.76/4.01  tff(c_284, plain, (![B_16, A_15, C_18]: (r1_tarski(B_16, k4_subset_1(A_15, B_16, C_18)) | ~m1_subset_1(k4_subset_1(A_15, B_16, C_18), k1_zfmisc_1(A_15)) | ~m1_subset_1(C_18, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_18, c_270])).
% 10.76/4.01  tff(c_4657, plain, (r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4524, c_284])).
% 10.76/4.01  tff(c_4676, plain, (r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4442, c_325, c_4524, c_4657])).
% 10.76/4.01  tff(c_5418, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_4676])).
% 10.76/4.01  tff(c_5421, plain, (~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_5418])).
% 10.76/4.01  tff(c_5425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_325, c_5421])).
% 10.76/4.01  tff(c_5427, plain, (m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_4676])).
% 10.76/4.01  tff(c_2448, plain, (![B_139]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', B_139))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', B_139)) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_325, c_2444])).
% 10.76/4.01  tff(c_2708, plain, (![B_146]: (k4_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', B_146))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', B_146)) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2448])).
% 10.76/4.01  tff(c_164, plain, (![A_33, B_34]: (k4_subset_1(u1_struct_0(A_33), k2_tops_1(A_33, B_34), k2_tops_1(A_33, k2_tops_1(A_33, B_34)))=k2_pre_topc(A_33, k2_tops_1(A_33, B_34)) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_28, c_153])).
% 10.76/4.01  tff(c_2715, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2708, c_164])).
% 10.76/4.01  tff(c_2750, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_36, c_34, c_2715])).
% 10.76/4.01  tff(c_12, plain, (![A_8, B_9, C_10]: (k4_subset_1(A_8, B_9, C_10)=k2_xboole_0(B_9, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.76/4.01  tff(c_7716, plain, (![B_215]: (k4_subset_1(u1_struct_0('#skF_1'), B_215, k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))=k2_xboole_0(B_215, k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_4442, c_12])).
% 10.76/4.01  tff(c_7764, plain, (![B_215]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0(B_215, k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), k3_subset_1(u1_struct_0('#skF_1'), B_215)) | ~m1_subset_1(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_7716, c_18])).
% 10.76/4.01  tff(c_7865, plain, (![B_216]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_xboole_0(B_216, k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), k3_subset_1(u1_struct_0('#skF_1'), B_216)) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_4442, c_7764])).
% 10.76/4.01  tff(c_7878, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2750, c_7865])).
% 10.76/4.01  tff(c_7884, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_7878])).
% 10.76/4.01  tff(c_14, plain, (![B_12, C_14, A_11]: (r1_tarski(B_12, C_14) | ~r1_tarski(k3_subset_1(A_11, C_14), k3_subset_1(A_11, B_12)) | ~m1_subset_1(C_14, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.76/4.01  tff(c_7922, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7884, c_14])).
% 10.76/4.01  tff(c_7931, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_5427, c_7922])).
% 10.76/4.01  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.76/4.01  tff(c_7938, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_7931, c_2])).
% 10.76/4.01  tff(c_7939, plain, (~r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_7938])).
% 10.76/4.01  tff(c_26, plain, (![A_30, B_32]: (k9_subset_1(u1_struct_0(A_30), k2_pre_topc(A_30, B_32), k2_pre_topc(A_30, k3_subset_1(u1_struct_0(A_30), B_32)))=k2_tops_1(A_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.76/4.01  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.76/4.01  tff(c_49, plain, (![A_48, B_49]: (k2_pre_topc(A_48, k2_pre_topc(A_48, B_49))=k2_pre_topc(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.76/4.01  tff(c_61, plain, (![A_48, B_7]: (k2_pre_topc(A_48, k2_pre_topc(A_48, k3_subset_1(u1_struct_0(A_48), B_7)))=k2_pre_topc(A_48, k3_subset_1(u1_struct_0(A_48), B_7)) | ~l1_pre_topc(A_48) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_48))))), inference(resolution, [status(thm)], [c_10, c_49])).
% 10.76/4.01  tff(c_324, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_264])).
% 10.76/4.01  tff(c_376, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_324, c_14])).
% 10.76/4.01  tff(c_381, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_376])).
% 10.76/4.01  tff(c_411, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_381])).
% 10.76/4.01  tff(c_414, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_411])).
% 10.76/4.01  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_414])).
% 10.76/4.01  tff(c_420, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_381])).
% 10.76/4.01  tff(c_58, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_49])).
% 10.76/4.01  tff(c_64, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_58])).
% 10.76/4.01  tff(c_489, plain, (![A_76, B_77, C_78]: (r1_tarski(k2_pre_topc(A_76, k9_subset_1(u1_struct_0(A_76), B_77, C_78)), k9_subset_1(u1_struct_0(A_76), k2_pre_topc(A_76, B_77), k2_pre_topc(A_76, C_78))) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.76/4.01  tff(c_4784, plain, (![A_188, B_189]: (r1_tarski(k2_pre_topc(A_188, k2_tops_1(A_188, B_189)), k9_subset_1(u1_struct_0(A_188), k2_pre_topc(A_188, k2_pre_topc(A_188, B_189)), k2_pre_topc(A_188, k2_pre_topc(A_188, k3_subset_1(u1_struct_0(A_188), B_189))))) | ~m1_subset_1(k2_pre_topc(A_188, k3_subset_1(u1_struct_0(A_188), B_189)), k1_zfmisc_1(u1_struct_0(A_188))) | ~m1_subset_1(k2_pre_topc(A_188, B_189), k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(superposition, [status(thm), theory('equality')], [c_26, c_489])).
% 10.76/4.01  tff(c_4845, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_64, c_4784])).
% 10.76/4.01  tff(c_4863, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_36, c_420, c_4845])).
% 10.76/4.01  tff(c_11625, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_4863])).
% 10.76/4.01  tff(c_11628, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_11625])).
% 10.76/4.01  tff(c_11631, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_11628])).
% 10.76/4.01  tff(c_11634, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_11631])).
% 10.76/4.01  tff(c_11638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_11634])).
% 10.76/4.01  tff(c_11639, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))))), inference(splitRight, [status(thm)], [c_4863])).
% 10.76/4.01  tff(c_12847, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_61, c_11639])).
% 10.76/4.01  tff(c_12851, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_12847])).
% 10.76/4.01  tff(c_12888, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_12851])).
% 10.76/4.01  tff(c_12892, plain, (r1_tarski(k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_12888])).
% 10.76/4.01  tff(c_12894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7939, c_12892])).
% 10.76/4.01  tff(c_12895, plain, (k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_7938])).
% 10.76/4.01  tff(c_5426, plain, (r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_pre_topc('#skF_1', k2_tops_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_4676])).
% 10.76/4.01  tff(c_12914, plain, (r1_tarski(k2_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12895, c_5426])).
% 10.76/4.01  tff(c_12940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_12914])).
% 10.76/4.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.76/4.01  
% 10.76/4.01  Inference rules
% 10.76/4.01  ----------------------
% 10.76/4.01  #Ref     : 0
% 10.76/4.01  #Sup     : 2792
% 10.76/4.02  #Fact    : 0
% 10.76/4.02  #Define  : 0
% 10.76/4.02  #Split   : 20
% 10.76/4.02  #Chain   : 0
% 10.76/4.02  #Close   : 0
% 10.76/4.02  
% 10.76/4.02  Ordering : KBO
% 10.76/4.02  
% 10.76/4.02  Simplification rules
% 10.76/4.02  ----------------------
% 10.76/4.02  #Subsume      : 230
% 10.76/4.02  #Demod        : 3482
% 10.76/4.02  #Tautology    : 1071
% 10.76/4.02  #SimpNegUnit  : 2
% 10.76/4.02  #BackRed      : 50
% 10.76/4.02  
% 10.76/4.02  #Partial instantiations: 0
% 10.76/4.02  #Strategies tried      : 1
% 10.76/4.02  
% 10.76/4.02  Timing (in seconds)
% 10.76/4.02  ----------------------
% 10.76/4.02  Preprocessing        : 0.35
% 10.76/4.02  Parsing              : 0.19
% 10.76/4.02  CNF conversion       : 0.02
% 10.76/4.02  Main loop            : 2.83
% 10.76/4.02  Inferencing          : 0.78
% 10.76/4.02  Reduction            : 1.18
% 10.76/4.02  Demodulation         : 0.91
% 10.76/4.02  BG Simplification    : 0.10
% 10.76/4.02  Subsumption          : 0.64
% 10.76/4.02  Abstraction          : 0.15
% 10.76/4.02  MUC search           : 0.00
% 10.76/4.02  Cooper               : 0.00
% 10.76/4.02  Total                : 3.22
% 10.76/4.02  Index Insertion      : 0.00
% 10.76/4.02  Index Deletion       : 0.00
% 10.76/4.02  Index Matching       : 0.00
% 10.76/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
