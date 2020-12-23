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
% DateTime   : Thu Dec  3 10:20:53 EST 2020

% Result     : Theorem 18.00s
% Output     : CNFRefutation 18.00s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 271 expanded)
%              Number of leaves         :   51 ( 111 expanded)
%              Depth                    :   17
%              Number of atoms          :  209 ( 487 expanded)
%              Number of equality atoms :   59 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_169,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_145,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_107,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_92,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_152,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_159,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_74,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_76,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_125,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(k3_subset_1(A,B),C)
           => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_70,plain,(
    ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_72,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_4239,plain,(
    ! [A_269,C_270,B_271] :
      ( r1_tarski(k2_pre_topc(A_269,C_270),B_271)
      | ~ r1_tarski(C_270,B_271)
      | ~ v4_pre_topc(B_271,A_269)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4268,plain,(
    ! [B_271] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),B_271)
      | ~ r1_tarski('#skF_3',B_271)
      | ~ v4_pre_topc(B_271,'#skF_2')
      | ~ m1_subset_1(B_271,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_74,c_4239])).

tff(c_20662,plain,(
    ! [B_472] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),B_472)
      | ~ r1_tarski('#skF_3',B_472)
      | ~ v4_pre_topc(B_472,'#skF_2')
      | ~ m1_subset_1(B_472,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4268])).

tff(c_20706,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_20662])).

tff(c_20725,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_12,c_20706])).

tff(c_1135,plain,(
    ! [A_159,B_160] :
      ( k4_xboole_0(A_159,B_160) = k3_subset_1(A_159,B_160)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1158,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1135])).

tff(c_54,plain,(
    ! [A_53,B_54] : k6_subset_1(A_53,B_54) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    ! [A_44,B_45] : m1_subset_1(k6_subset_1(A_44,B_45),k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_77,plain,(
    ! [A_44,B_45] : m1_subset_1(k4_xboole_0(A_44,B_45),k1_zfmisc_1(A_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_1369,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_77])).

tff(c_2863,plain,(
    ! [A_221,B_222] :
      ( k2_tops_1(A_221,k3_subset_1(u1_struct_0(A_221),B_222)) = k2_tops_1(A_221,B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2890,plain,
    ( k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_2863])).

tff(c_2906,plain,(
    k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2890])).

tff(c_62,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k2_tops_1(A_65,B_66),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3496,plain,
    ( m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2906,c_62])).

tff(c_3500,plain,(
    m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1369,c_3496])).

tff(c_3299,plain,(
    ! [A_234,B_235] :
      ( k4_subset_1(u1_struct_0(A_234),B_235,k2_tops_1(A_234,B_235)) = k2_pre_topc(A_234,B_235)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_3326,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_3299])).

tff(c_3340,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3326])).

tff(c_46,plain,(
    ! [A_41,B_42,C_43] :
      ( m1_subset_1(k4_subset_1(A_41,B_42,C_43),k1_zfmisc_1(A_41))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6701,plain,
    ( m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3340,c_46])).

tff(c_6707,plain,(
    m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3500,c_6701])).

tff(c_28,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1071,plain,(
    ! [C_154,A_155,B_156] :
      ( r2_hidden(C_154,A_155)
      | ~ r2_hidden(C_154,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16686,plain,(
    ! [A_436,B_437,A_438] :
      ( r2_hidden('#skF_1'(A_436,B_437),A_438)
      | ~ m1_subset_1(A_436,k1_zfmisc_1(A_438))
      | r1_tarski(A_436,B_437) ) ),
    inference(resolution,[status(thm)],[c_6,c_1071])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16698,plain,(
    ! [A_439,A_440] :
      ( ~ m1_subset_1(A_439,k1_zfmisc_1(A_440))
      | r1_tarski(A_439,A_440) ) ),
    inference(resolution,[status(thm)],[c_16686,c_4])).

tff(c_16762,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_16698])).

tff(c_38,plain,(
    ! [B_34,A_33] : k2_tarski(B_34,A_33) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_231,plain,(
    ! [A_105,B_106] : k3_tarski(k2_tarski(A_105,B_106)) = k2_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_274,plain,(
    ! [B_111,A_112] : k3_tarski(k2_tarski(B_111,A_112)) = k2_xboole_0(A_112,B_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_231])).

tff(c_40,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_297,plain,(
    ! [B_113,A_114] : k2_xboole_0(B_113,A_114) = k2_xboole_0(A_114,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_40])).

tff(c_22,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_144,plain,(
    ! [A_97,B_98] :
      ( k2_xboole_0(A_97,B_98) = B_98
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_163,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(resolution,[status(thm)],[c_22,c_144])).

tff(c_329,plain,(
    ! [B_113] : k2_xboole_0(B_113,k1_xboole_0) = B_113 ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_163])).

tff(c_984,plain,(
    ! [A_149,B_150,C_151] :
      ( r1_tarski(k4_xboole_0(A_149,B_150),C_151)
      | ~ r1_tarski(A_149,k2_xboole_0(B_150,C_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_538,plain,(
    ! [B_124,A_125] :
      ( B_124 = A_125
      | ~ r1_tarski(B_124,A_125)
      | ~ r1_tarski(A_125,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_555,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_538])).

tff(c_988,plain,(
    ! [A_149,B_150] :
      ( k4_xboole_0(A_149,B_150) = k1_xboole_0
      | ~ r1_tarski(A_149,k2_xboole_0(B_150,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_984,c_555])).

tff(c_1008,plain,(
    ! [A_149,B_150] :
      ( k4_xboole_0(A_149,B_150) = k1_xboole_0
      | ~ r1_tarski(A_149,B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_988])).

tff(c_16775,plain,(
    k4_xboole_0('#skF_3',u1_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16762,c_1008])).

tff(c_34,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16859,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_2')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16775,c_34])).

tff(c_16901,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_16859])).

tff(c_259,plain,(
    ! [A_109,B_110] : k1_setfam_1(k2_tarski(A_109,B_110)) = k3_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_831,plain,(
    ! [B_144,A_145] : k1_setfam_1(k2_tarski(B_144,A_145)) = k3_xboole_0(A_145,B_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_259])).

tff(c_60,plain,(
    ! [A_63,B_64] : k1_setfam_1(k2_tarski(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_837,plain,(
    ! [B_144,A_145] : k3_xboole_0(B_144,A_145) = k3_xboole_0(A_145,B_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_831,c_60])).

tff(c_1360,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k3_xboole_0(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1158,c_34])).

tff(c_1375,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k3_xboole_0('#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_1360])).

tff(c_60403,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16901,c_1375])).

tff(c_1237,plain,(
    ! [A_166,B_167] :
      ( m1_subset_1(k3_subset_1(A_166,B_167),k1_zfmisc_1(A_166))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k3_subset_1(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_19003,plain,(
    ! [A_456,B_457] :
      ( k4_xboole_0(A_456,k3_subset_1(A_456,B_457)) = k3_subset_1(A_456,k3_subset_1(A_456,B_457))
      | ~ m1_subset_1(B_457,k1_zfmisc_1(A_456)) ) ),
    inference(resolution,[status(thm)],[c_1237,c_42])).

tff(c_19048,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_19003])).

tff(c_60404,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60403,c_19048])).

tff(c_58,plain,(
    ! [A_59,B_60,C_62] :
      ( r1_tarski(k3_subset_1(A_59,k4_subset_1(A_59,B_60,C_62)),k3_subset_1(A_59,B_60))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6698,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3340,c_58])).

tff(c_6705,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3')),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3500,c_6698])).

tff(c_56,plain,(
    ! [A_55,C_58,B_56] :
      ( r1_tarski(k3_subset_1(A_55,C_58),B_56)
      | ~ r1_tarski(k3_subset_1(A_55,B_56),C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_63966,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6705,c_56])).

tff(c_63980,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6707,c_1369,c_60404,c_63966])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63997,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_63980,c_8])).

tff(c_64009,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20725,c_63997])).

tff(c_64049,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64009,c_3340])).

tff(c_2061,plain,(
    ! [A_200,B_201,C_202] :
      ( k4_subset_1(A_200,B_201,C_202) = k2_xboole_0(B_201,C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(A_200))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(A_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_25944,plain,(
    ! [A_520,B_521,B_522] :
      ( k4_subset_1(u1_struct_0(A_520),B_521,k2_tops_1(A_520,B_522)) = k2_xboole_0(B_521,k2_tops_1(A_520,B_522))
      | ~ m1_subset_1(B_521,k1_zfmisc_1(u1_struct_0(A_520)))
      | ~ m1_subset_1(B_522,k1_zfmisc_1(u1_struct_0(A_520)))
      | ~ l1_pre_topc(A_520) ) ),
    inference(resolution,[status(thm)],[c_62,c_2061])).

tff(c_25977,plain,(
    ! [B_522] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_522)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_522))
      | ~ m1_subset_1(B_522,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_74,c_25944])).

tff(c_73379,plain,(
    ! [B_810] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_810)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_810))
      | ~ m1_subset_1(B_810,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_25977])).

tff(c_73405,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1369,c_73379])).

tff(c_73451,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64049,c_2906,c_2906,c_73405])).

tff(c_36,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_339,plain,(
    ! [B_113,A_114] : r1_tarski(B_113,k2_xboole_0(A_114,B_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_36])).

tff(c_73656,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_73451,c_339])).

tff(c_73706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_73656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.00/10.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.00/10.45  
% 18.00/10.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.00/10.45  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 18.00/10.45  
% 18.00/10.45  %Foreground sorts:
% 18.00/10.45  
% 18.00/10.45  
% 18.00/10.45  %Background operators:
% 18.00/10.45  
% 18.00/10.45  
% 18.00/10.45  %Foreground operators:
% 18.00/10.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.00/10.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.00/10.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.00/10.45  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 18.00/10.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.00/10.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 18.00/10.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.00/10.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.00/10.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.00/10.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 18.00/10.45  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 18.00/10.45  tff('#skF_2', type, '#skF_2': $i).
% 18.00/10.45  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 18.00/10.45  tff('#skF_3', type, '#skF_3': $i).
% 18.00/10.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.00/10.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 18.00/10.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.00/10.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.00/10.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.00/10.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.00/10.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.00/10.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.00/10.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.00/10.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 18.00/10.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.00/10.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.00/10.45  
% 18.00/10.47  tff(f_169, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 18.00/10.47  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.00/10.47  tff(f_145, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_1)).
% 18.00/10.47  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 18.00/10.47  tff(f_107, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 18.00/10.47  tff(f_92, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 18.00/10.47  tff(f_152, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 18.00/10.47  tff(f_131, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 18.00/10.47  tff(f_159, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 18.00/10.47  tff(f_90, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 18.00/10.47  tff(f_60, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 18.00/10.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 18.00/10.47  tff(f_99, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 18.00/10.47  tff(f_74, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 18.00/10.47  tff(f_76, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 18.00/10.47  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 18.00/10.47  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.00/10.47  tff(f_64, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 18.00/10.47  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.00/10.47  tff(f_125, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 18.00/10.47  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 18.00/10.47  tff(f_123, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 18.00/10.47  tff(f_116, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 18.00/10.47  tff(f_105, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 18.00/10.47  tff(f_72, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.00/10.47  tff(c_70, plain, (~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 18.00/10.47  tff(c_72, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 18.00/10.47  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.00/10.47  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 18.00/10.47  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 18.00/10.47  tff(c_4239, plain, (![A_269, C_270, B_271]: (r1_tarski(k2_pre_topc(A_269, C_270), B_271) | ~r1_tarski(C_270, B_271) | ~v4_pre_topc(B_271, A_269) | ~m1_subset_1(C_270, k1_zfmisc_1(u1_struct_0(A_269))) | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0(A_269))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_145])).
% 18.00/10.47  tff(c_4268, plain, (![B_271]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), B_271) | ~r1_tarski('#skF_3', B_271) | ~v4_pre_topc(B_271, '#skF_2') | ~m1_subset_1(B_271, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_74, c_4239])).
% 18.00/10.47  tff(c_20662, plain, (![B_472]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), B_472) | ~r1_tarski('#skF_3', B_472) | ~v4_pre_topc(B_472, '#skF_2') | ~m1_subset_1(B_472, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4268])).
% 18.00/10.47  tff(c_20706, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_20662])).
% 18.00/10.47  tff(c_20725, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_12, c_20706])).
% 18.00/10.47  tff(c_1135, plain, (![A_159, B_160]: (k4_xboole_0(A_159, B_160)=k3_subset_1(A_159, B_160) | ~m1_subset_1(B_160, k1_zfmisc_1(A_159)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.00/10.47  tff(c_1158, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_74, c_1135])).
% 18.00/10.47  tff(c_54, plain, (![A_53, B_54]: (k6_subset_1(A_53, B_54)=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.00/10.47  tff(c_48, plain, (![A_44, B_45]: (m1_subset_1(k6_subset_1(A_44, B_45), k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 18.00/10.47  tff(c_77, plain, (![A_44, B_45]: (m1_subset_1(k4_xboole_0(A_44, B_45), k1_zfmisc_1(A_44)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 18.00/10.47  tff(c_1369, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1158, c_77])).
% 18.00/10.47  tff(c_2863, plain, (![A_221, B_222]: (k2_tops_1(A_221, k3_subset_1(u1_struct_0(A_221), B_222))=k2_tops_1(A_221, B_222) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_152])).
% 18.00/10.47  tff(c_2890, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_74, c_2863])).
% 18.00/10.47  tff(c_2906, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2890])).
% 18.00/10.47  tff(c_62, plain, (![A_65, B_66]: (m1_subset_1(k2_tops_1(A_65, B_66), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_131])).
% 18.00/10.47  tff(c_3496, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2906, c_62])).
% 18.00/10.47  tff(c_3500, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1369, c_3496])).
% 18.00/10.47  tff(c_3299, plain, (![A_234, B_235]: (k4_subset_1(u1_struct_0(A_234), B_235, k2_tops_1(A_234, B_235))=k2_pre_topc(A_234, B_235) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234))), inference(cnfTransformation, [status(thm)], [f_159])).
% 18.00/10.47  tff(c_3326, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_74, c_3299])).
% 18.00/10.47  tff(c_3340, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3326])).
% 18.00/10.47  tff(c_46, plain, (![A_41, B_42, C_43]: (m1_subset_1(k4_subset_1(A_41, B_42, C_43), k1_zfmisc_1(A_41)) | ~m1_subset_1(C_43, k1_zfmisc_1(A_41)) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 18.00/10.47  tff(c_6701, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3340, c_46])).
% 18.00/10.47  tff(c_6707, plain, (m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3500, c_6701])).
% 18.00/10.47  tff(c_28, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.00/10.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 18.00/10.47  tff(c_1071, plain, (![C_154, A_155, B_156]: (r2_hidden(C_154, A_155) | ~r2_hidden(C_154, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.00/10.47  tff(c_16686, plain, (![A_436, B_437, A_438]: (r2_hidden('#skF_1'(A_436, B_437), A_438) | ~m1_subset_1(A_436, k1_zfmisc_1(A_438)) | r1_tarski(A_436, B_437))), inference(resolution, [status(thm)], [c_6, c_1071])).
% 18.00/10.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 18.00/10.47  tff(c_16698, plain, (![A_439, A_440]: (~m1_subset_1(A_439, k1_zfmisc_1(A_440)) | r1_tarski(A_439, A_440))), inference(resolution, [status(thm)], [c_16686, c_4])).
% 18.00/10.47  tff(c_16762, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_74, c_16698])).
% 18.00/10.47  tff(c_38, plain, (![B_34, A_33]: (k2_tarski(B_34, A_33)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_74])).
% 18.00/10.47  tff(c_231, plain, (![A_105, B_106]: (k3_tarski(k2_tarski(A_105, B_106))=k2_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.00/10.47  tff(c_274, plain, (![B_111, A_112]: (k3_tarski(k2_tarski(B_111, A_112))=k2_xboole_0(A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_38, c_231])).
% 18.00/10.47  tff(c_40, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.00/10.47  tff(c_297, plain, (![B_113, A_114]: (k2_xboole_0(B_113, A_114)=k2_xboole_0(A_114, B_113))), inference(superposition, [status(thm), theory('equality')], [c_274, c_40])).
% 18.00/10.47  tff(c_22, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.00/10.47  tff(c_144, plain, (![A_97, B_98]: (k2_xboole_0(A_97, B_98)=B_98 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.00/10.47  tff(c_163, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(resolution, [status(thm)], [c_22, c_144])).
% 18.00/10.47  tff(c_329, plain, (![B_113]: (k2_xboole_0(B_113, k1_xboole_0)=B_113)), inference(superposition, [status(thm), theory('equality')], [c_297, c_163])).
% 18.00/10.47  tff(c_984, plain, (![A_149, B_150, C_151]: (r1_tarski(k4_xboole_0(A_149, B_150), C_151) | ~r1_tarski(A_149, k2_xboole_0(B_150, C_151)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 18.00/10.47  tff(c_538, plain, (![B_124, A_125]: (B_124=A_125 | ~r1_tarski(B_124, A_125) | ~r1_tarski(A_125, B_124))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.00/10.47  tff(c_555, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_538])).
% 18.00/10.47  tff(c_988, plain, (![A_149, B_150]: (k4_xboole_0(A_149, B_150)=k1_xboole_0 | ~r1_tarski(A_149, k2_xboole_0(B_150, k1_xboole_0)))), inference(resolution, [status(thm)], [c_984, c_555])).
% 18.00/10.47  tff(c_1008, plain, (![A_149, B_150]: (k4_xboole_0(A_149, B_150)=k1_xboole_0 | ~r1_tarski(A_149, B_150))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_988])).
% 18.00/10.47  tff(c_16775, plain, (k4_xboole_0('#skF_3', u1_struct_0('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_16762, c_1008])).
% 18.00/10.47  tff(c_34, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 18.00/10.47  tff(c_16859, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_2'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16775, c_34])).
% 18.00/10.47  tff(c_16901, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_16859])).
% 18.00/10.47  tff(c_259, plain, (![A_109, B_110]: (k1_setfam_1(k2_tarski(A_109, B_110))=k3_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_125])).
% 18.00/10.47  tff(c_831, plain, (![B_144, A_145]: (k1_setfam_1(k2_tarski(B_144, A_145))=k3_xboole_0(A_145, B_144))), inference(superposition, [status(thm), theory('equality')], [c_38, c_259])).
% 18.00/10.47  tff(c_60, plain, (![A_63, B_64]: (k1_setfam_1(k2_tarski(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_125])).
% 18.00/10.47  tff(c_837, plain, (![B_144, A_145]: (k3_xboole_0(B_144, A_145)=k3_xboole_0(A_145, B_144))), inference(superposition, [status(thm), theory('equality')], [c_831, c_60])).
% 18.00/10.47  tff(c_1360, plain, (k4_xboole_0(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k3_xboole_0(u1_struct_0('#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1158, c_34])).
% 18.00/10.47  tff(c_1375, plain, (k4_xboole_0(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k3_xboole_0('#skF_3', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_837, c_1360])).
% 18.00/10.47  tff(c_60403, plain, (k4_xboole_0(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16901, c_1375])).
% 18.00/10.47  tff(c_1237, plain, (![A_166, B_167]: (m1_subset_1(k3_subset_1(A_166, B_167), k1_zfmisc_1(A_166)) | ~m1_subset_1(B_167, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 18.00/10.47  tff(c_42, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k3_subset_1(A_37, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.00/10.47  tff(c_19003, plain, (![A_456, B_457]: (k4_xboole_0(A_456, k3_subset_1(A_456, B_457))=k3_subset_1(A_456, k3_subset_1(A_456, B_457)) | ~m1_subset_1(B_457, k1_zfmisc_1(A_456)))), inference(resolution, [status(thm)], [c_1237, c_42])).
% 18.00/10.47  tff(c_19048, plain, (k4_xboole_0(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_19003])).
% 18.00/10.47  tff(c_60404, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60403, c_19048])).
% 18.00/10.47  tff(c_58, plain, (![A_59, B_60, C_62]: (r1_tarski(k3_subset_1(A_59, k4_subset_1(A_59, B_60, C_62)), k3_subset_1(A_59, B_60)) | ~m1_subset_1(C_62, k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 18.00/10.47  tff(c_6698, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3')), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3340, c_58])).
% 18.00/10.47  tff(c_6705, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3')), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3500, c_6698])).
% 18.00/10.47  tff(c_56, plain, (![A_55, C_58, B_56]: (r1_tarski(k3_subset_1(A_55, C_58), B_56) | ~r1_tarski(k3_subset_1(A_55, B_56), C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 18.00/10.47  tff(c_63966, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6705, c_56])).
% 18.00/10.47  tff(c_63980, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6707, c_1369, c_60404, c_63966])).
% 18.00/10.47  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.00/10.47  tff(c_63997, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_63980, c_8])).
% 18.00/10.47  tff(c_64009, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20725, c_63997])).
% 18.00/10.47  tff(c_64049, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64009, c_3340])).
% 18.00/10.47  tff(c_2061, plain, (![A_200, B_201, C_202]: (k4_subset_1(A_200, B_201, C_202)=k2_xboole_0(B_201, C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(A_200)) | ~m1_subset_1(B_201, k1_zfmisc_1(A_200)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 18.00/10.47  tff(c_25944, plain, (![A_520, B_521, B_522]: (k4_subset_1(u1_struct_0(A_520), B_521, k2_tops_1(A_520, B_522))=k2_xboole_0(B_521, k2_tops_1(A_520, B_522)) | ~m1_subset_1(B_521, k1_zfmisc_1(u1_struct_0(A_520))) | ~m1_subset_1(B_522, k1_zfmisc_1(u1_struct_0(A_520))) | ~l1_pre_topc(A_520))), inference(resolution, [status(thm)], [c_62, c_2061])).
% 18.00/10.47  tff(c_25977, plain, (![B_522]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_522))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_522)) | ~m1_subset_1(B_522, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_74, c_25944])).
% 18.00/10.47  tff(c_73379, plain, (![B_810]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_810))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_810)) | ~m1_subset_1(B_810, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_25977])).
% 18.00/10.47  tff(c_73405, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))), inference(resolution, [status(thm)], [c_1369, c_73379])).
% 18.00/10.47  tff(c_73451, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64049, c_2906, c_2906, c_73405])).
% 18.00/10.47  tff(c_36, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 18.00/10.47  tff(c_339, plain, (![B_113, A_114]: (r1_tarski(B_113, k2_xboole_0(A_114, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_297, c_36])).
% 18.00/10.47  tff(c_73656, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_73451, c_339])).
% 18.00/10.47  tff(c_73706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_73656])).
% 18.00/10.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.00/10.47  
% 18.00/10.47  Inference rules
% 18.00/10.47  ----------------------
% 18.00/10.47  #Ref     : 0
% 18.00/10.47  #Sup     : 18058
% 18.00/10.47  #Fact    : 0
% 18.00/10.47  #Define  : 0
% 18.00/10.47  #Split   : 5
% 18.00/10.47  #Chain   : 0
% 18.00/10.47  #Close   : 0
% 18.00/10.47  
% 18.00/10.47  Ordering : KBO
% 18.00/10.47  
% 18.00/10.47  Simplification rules
% 18.00/10.47  ----------------------
% 18.00/10.47  #Subsume      : 789
% 18.00/10.47  #Demod        : 18017
% 18.00/10.47  #Tautology    : 12317
% 18.00/10.47  #SimpNegUnit  : 2
% 18.00/10.47  #BackRed      : 69
% 18.00/10.47  
% 18.00/10.47  #Partial instantiations: 0
% 18.00/10.47  #Strategies tried      : 1
% 18.00/10.47  
% 18.00/10.47  Timing (in seconds)
% 18.00/10.47  ----------------------
% 18.00/10.48  Preprocessing        : 0.35
% 18.00/10.48  Parsing              : 0.18
% 18.00/10.48  CNF conversion       : 0.03
% 18.00/10.48  Main loop            : 9.30
% 18.00/10.48  Inferencing          : 1.25
% 18.00/10.48  Reduction            : 5.50
% 18.00/10.48  Demodulation         : 4.89
% 18.00/10.48  BG Simplification    : 0.13
% 18.00/10.48  Subsumption          : 2.02
% 18.00/10.48  Abstraction          : 0.22
% 18.00/10.48  MUC search           : 0.00
% 18.00/10.48  Cooper               : 0.00
% 18.00/10.48  Total                : 9.69
% 18.00/10.48  Index Insertion      : 0.00
% 18.00/10.48  Index Deletion       : 0.00
% 18.00/10.48  Index Matching       : 0.00
% 18.00/10.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
