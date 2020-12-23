%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:53 EST 2020

% Result     : Theorem 13.29s
% Output     : CNFRefutation 13.29s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 551 expanded)
%              Number of leaves         :   31 ( 205 expanded)
%              Depth                    :   16
%              Number of atoms          :  281 (1833 expanded)
%              Number of equality atoms :   31 ( 331 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( B = k1_xboole_0
               => ( v2_compts_1(B,A)
                <=> v1_compts_1(k1_pre_topc(A,B)) ) )
              & ( v2_pre_topc(A)
               => ( B = k1_xboole_0
                  | ( v2_compts_1(B,A)
                  <=> v1_compts_1(k1_pre_topc(A,B)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_25312,plain,(
    ! [A_636,B_637] :
      ( m1_pre_topc(k1_pre_topc(A_636,B_637),A_636)
      | ~ m1_subset_1(B_637,k1_zfmisc_1(u1_struct_0(A_636)))
      | ~ l1_pre_topc(A_636) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25320,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_25312])).

tff(c_25328,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_25320])).

tff(c_44,plain,
    ( ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_117,plain,(
    ~ v2_compts_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_256,plain,(
    ! [A_72,B_73] :
      ( m1_pre_topc(k1_pre_topc(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_264,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_256])).

tff(c_272,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_264])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_60,B_61] :
      ( v1_pre_topc(k1_pre_topc(A_60,B_61))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_134,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_131])).

tff(c_141,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_134])).

tff(c_723,plain,(
    ! [A_103,B_104] :
      ( k2_struct_0(k1_pre_topc(A_103,B_104)) = B_104
      | ~ m1_pre_topc(k1_pre_topc(A_103,B_104),A_103)
      | ~ v1_pre_topc(k1_pre_topc(A_103,B_104))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_733,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_272,c_723])).

tff(c_744,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_141,c_733])).

tff(c_144,plain,(
    ! [A_63,B_64] :
      ( u1_struct_0(k1_pre_topc(A_63,B_64)) = B_64
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_147,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_144])).

tff(c_154,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_147])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_142,plain,(
    ! [A_60] :
      ( v1_pre_topc(k1_pre_topc(A_60,u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_101,c_131])).

tff(c_162,plain,
    ( v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_142])).

tff(c_197,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_198,plain,(
    ! [A_66,B_67] :
      ( m1_pre_topc(k1_pre_topc(A_66,B_67),A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_204,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_198])).

tff(c_210,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_204])).

tff(c_20,plain,(
    ! [B_16,A_14] :
      ( l1_pre_topc(B_16)
      | ~ m1_pre_topc(B_16,A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_226,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_210,c_20])).

tff(c_229,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_226])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_229])).

tff(c_233,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_80,plain,
    ( v2_compts_1('#skF_3','#skF_2')
    | v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_116,plain,(
    v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_28,plain,(
    ! [A_27] :
      ( v2_compts_1(k2_struct_0(A_27),A_27)
      | ~ v1_compts_1(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_754,plain,
    ( v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_28])).

tff(c_762,plain,(
    v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_116,c_754])).

tff(c_262,plain,(
    ! [B_73] :
      ( m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),B_73),k1_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_73,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_256])).

tff(c_269,plain,(
    ! [B_73] :
      ( m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),B_73),k1_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_73,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_262])).

tff(c_22,plain,(
    ! [A_17,B_19] :
      ( u1_struct_0(k1_pre_topc(A_17,B_19)) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_159,plain,(
    ! [B_19] :
      ( u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),B_19)) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_22])).

tff(c_5101,plain,(
    ! [B_19] :
      ( u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),B_19)) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_159])).

tff(c_308,plain,(
    ! [C_76,A_77,B_78] :
      ( m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(B_78)))
      | ~ m1_pre_topc(B_78,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_422,plain,(
    ! [B_84,A_85] :
      ( m1_subset_1(u1_struct_0(B_84),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_pre_topc(B_84,A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_101,c_308])).

tff(c_24,plain,(
    ! [C_26,A_20,B_24] :
      ( m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(B_24)))
      | ~ m1_pre_topc(B_24,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6650,plain,(
    ! [B_280,A_281,A_282] :
      ( m1_subset_1(u1_struct_0(B_280),k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ m1_pre_topc(A_282,A_281)
      | ~ l1_pre_topc(A_281)
      | ~ m1_pre_topc(B_280,A_282)
      | ~ l1_pre_topc(A_282) ) ),
    inference(resolution,[status(thm)],[c_422,c_24])).

tff(c_6662,plain,(
    ! [B_280] :
      ( m1_subset_1(u1_struct_0(B_280),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_280,k1_pre_topc('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_272,c_6650])).

tff(c_6675,plain,(
    ! [B_283] :
      ( m1_subset_1(u1_struct_0(B_283),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_283,k1_pre_topc('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_40,c_6662])).

tff(c_13348,plain,(
    ! [B_421] :
      ( m1_subset_1(B_421,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),B_421),k1_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_421,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5101,c_6675])).

tff(c_13408,plain,(
    ! [B_422] :
      ( m1_subset_1(B_422,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_422,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_269,c_13348])).

tff(c_846,plain,(
    ! [A_109,B_110,C_111] :
      ( '#skF_1'(A_109,B_110,C_111) = C_111
      | v2_compts_1(C_111,A_109)
      | ~ r1_tarski(C_111,k2_struct_0(B_110))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_pre_topc(B_110,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_854,plain,(
    ! [A_109,B_110] :
      ( '#skF_1'(A_109,B_110,k2_struct_0(B_110)) = k2_struct_0(B_110)
      | v2_compts_1(k2_struct_0(B_110),A_109)
      | ~ m1_subset_1(k2_struct_0(B_110),k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_pre_topc(B_110,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_846])).

tff(c_13419,plain,(
    ! [B_110] :
      ( '#skF_1'('#skF_2',B_110,k2_struct_0(B_110)) = k2_struct_0(B_110)
      | v2_compts_1(k2_struct_0(B_110),'#skF_2')
      | ~ m1_pre_topc(B_110,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1(k2_struct_0(B_110),k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_13408,c_854])).

tff(c_25027,plain,(
    ! [B_622] :
      ( '#skF_1'('#skF_2',B_622,k2_struct_0(B_622)) = k2_struct_0(B_622)
      | v2_compts_1(k2_struct_0(B_622),'#skF_2')
      | ~ m1_pre_topc(B_622,'#skF_2')
      | ~ m1_subset_1(k2_struct_0(B_622),k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_13419])).

tff(c_25049,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),k2_struct_0(k1_pre_topc('#skF_2','#skF_3'))) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1(k2_struct_0(k1_pre_topc('#skF_2','#skF_3')),'#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_25027])).

tff(c_25071,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3') = '#skF_3'
    | v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_272,c_744,c_744,c_744,c_25049])).

tff(c_25072,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_25071])).

tff(c_32,plain,(
    ! [A_28,B_40,C_46] :
      ( ~ v2_compts_1('#skF_1'(A_28,B_40,C_46),B_40)
      | v2_compts_1(C_46,A_28)
      | ~ r1_tarski(C_46,k2_struct_0(B_40))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_pre_topc(B_40,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_25126,plain,
    ( ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25072,c_32])).

tff(c_25176,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_272,c_38,c_6,c_744,c_762,c_25126])).

tff(c_25178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_25176])).

tff(c_25179,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_25181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25179,c_116])).

tff(c_25182,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_25183,plain,(
    ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_25212,plain,(
    ! [A_630,B_631] :
      ( u1_struct_0(k1_pre_topc(A_630,B_631)) = B_631
      | ~ m1_subset_1(B_631,k1_zfmisc_1(u1_struct_0(A_630)))
      | ~ l1_pre_topc(A_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_25215,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_25212])).

tff(c_25222,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_25215])).

tff(c_25199,plain,(
    ! [A_627,B_628] :
      ( v1_pre_topc(k1_pre_topc(A_627,B_628))
      | ~ m1_subset_1(B_628,k1_zfmisc_1(u1_struct_0(A_627)))
      | ~ l1_pre_topc(A_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25210,plain,(
    ! [A_627] :
      ( v1_pre_topc(k1_pre_topc(A_627,u1_struct_0(A_627)))
      | ~ l1_pre_topc(A_627) ) ),
    inference(resolution,[status(thm)],[c_101,c_25199])).

tff(c_25230,plain,
    ( v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25222,c_25210])).

tff(c_25265,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_25230])).

tff(c_25266,plain,(
    ! [A_633,B_634] :
      ( m1_pre_topc(k1_pre_topc(A_633,B_634),A_633)
      | ~ m1_subset_1(B_634,k1_zfmisc_1(u1_struct_0(A_633)))
      | ~ l1_pre_topc(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25272,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_25266])).

tff(c_25278,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_25272])).

tff(c_25282,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_25278,c_20])).

tff(c_25285,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_25282])).

tff(c_25287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25265,c_25285])).

tff(c_25289,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_25230])).

tff(c_25202,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_25199])).

tff(c_25209,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_25202])).

tff(c_25765,plain,(
    ! [A_666,B_667] :
      ( k2_struct_0(k1_pre_topc(A_666,B_667)) = B_667
      | ~ m1_pre_topc(k1_pre_topc(A_666,B_667),A_666)
      | ~ v1_pre_topc(k1_pre_topc(A_666,B_667))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0(A_666)))
      | ~ l1_pre_topc(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_25775,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_25328,c_25765])).

tff(c_25786,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_25209,c_25775])).

tff(c_26,plain,(
    ! [A_27] :
      ( v1_compts_1(A_27)
      | ~ v2_compts_1(k2_struct_0(A_27),A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_25796,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_25786,c_26])).

tff(c_25804,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25289,c_25796])).

tff(c_25805,plain,(
    ~ v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_25183,c_25804])).

tff(c_26268,plain,(
    ! [D_690,B_691,A_692] :
      ( v2_compts_1(D_690,B_691)
      | ~ m1_subset_1(D_690,k1_zfmisc_1(u1_struct_0(B_691)))
      | ~ v2_compts_1(D_690,A_692)
      | ~ r1_tarski(D_690,k2_struct_0(B_691))
      | ~ m1_subset_1(D_690,k1_zfmisc_1(u1_struct_0(A_692)))
      | ~ m1_pre_topc(B_691,A_692)
      | ~ l1_pre_topc(A_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_27119,plain,(
    ! [B_710,A_711] :
      ( v2_compts_1(u1_struct_0(B_710),B_710)
      | ~ v2_compts_1(u1_struct_0(B_710),A_711)
      | ~ r1_tarski(u1_struct_0(B_710),k2_struct_0(B_710))
      | ~ m1_subset_1(u1_struct_0(B_710),k1_zfmisc_1(u1_struct_0(A_711)))
      | ~ m1_pre_topc(B_710,A_711)
      | ~ l1_pre_topc(A_711) ) ),
    inference(resolution,[status(thm)],[c_101,c_26268])).

tff(c_27149,plain,(
    ! [A_711] :
      ( v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),k1_pre_topc('#skF_2','#skF_3'))
      | ~ v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),A_711)
      | ~ r1_tarski('#skF_3',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
      | ~ m1_subset_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0(A_711)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_711)
      | ~ l1_pre_topc(A_711) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25222,c_27119])).

tff(c_27172,plain,(
    ! [A_711] :
      ( v2_compts_1('#skF_3',k1_pre_topc('#skF_2','#skF_3'))
      | ~ v2_compts_1('#skF_3',A_711)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_711)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_711)
      | ~ l1_pre_topc(A_711) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25222,c_6,c_25786,c_25222,c_25222,c_27149])).

tff(c_27174,plain,(
    ! [A_712] :
      ( ~ v2_compts_1('#skF_3',A_712)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_712)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_712)
      | ~ l1_pre_topc(A_712) ) ),
    inference(negUnitSimplification,[status(thm)],[c_25805,c_27172])).

tff(c_27217,plain,
    ( ~ v2_compts_1('#skF_3','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_27174])).

tff(c_27239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_25328,c_25182,c_27217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.29/5.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.29/5.96  
% 13.29/5.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.29/5.97  %$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 13.29/5.97  
% 13.29/5.97  %Foreground sorts:
% 13.29/5.97  
% 13.29/5.97  
% 13.29/5.97  %Background operators:
% 13.29/5.97  
% 13.29/5.97  
% 13.29/5.97  %Foreground operators:
% 13.29/5.97  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 13.29/5.97  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 13.29/5.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.29/5.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.29/5.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.29/5.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.29/5.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.29/5.97  tff('#skF_2', type, '#skF_2': $i).
% 13.29/5.97  tff('#skF_3', type, '#skF_3': $i).
% 13.29/5.97  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 13.29/5.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.29/5.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.29/5.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.29/5.97  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 13.29/5.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.29/5.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.29/5.97  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 13.29/5.97  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 13.29/5.97  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 13.29/5.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.29/5.97  
% 13.29/5.99  tff(f_126, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (((B = k1_xboole_0) => (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))) & (v2_pre_topc(A) => ((B = k1_xboole_0) | (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_compts_1)).
% 13.29/5.99  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 13.29/5.99  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.29/5.99  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 13.29/5.99  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 13.29/5.99  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 13.29/5.99  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 13.29/5.99  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 13.29/5.99  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (v1_compts_1(A) <=> v2_compts_1(k2_struct_0(A), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_compts_1)).
% 13.29/5.99  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 13.29/5.99  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_compts_1)).
% 13.29/5.99  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.29/5.99  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.29/5.99  tff(c_25312, plain, (![A_636, B_637]: (m1_pre_topc(k1_pre_topc(A_636, B_637), A_636) | ~m1_subset_1(B_637, k1_zfmisc_1(u1_struct_0(A_636))) | ~l1_pre_topc(A_636))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.29/5.99  tff(c_25320, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_25312])).
% 13.29/5.99  tff(c_25328, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_25320])).
% 13.29/5.99  tff(c_44, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.29/5.99  tff(c_117, plain, (~v2_compts_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 13.29/5.99  tff(c_256, plain, (![A_72, B_73]: (m1_pre_topc(k1_pre_topc(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.29/5.99  tff(c_264, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_256])).
% 13.29/5.99  tff(c_272, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_264])).
% 13.29/5.99  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.29/5.99  tff(c_131, plain, (![A_60, B_61]: (v1_pre_topc(k1_pre_topc(A_60, B_61)) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.29/5.99  tff(c_134, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_131])).
% 13.29/5.99  tff(c_141, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_134])).
% 13.29/5.99  tff(c_723, plain, (![A_103, B_104]: (k2_struct_0(k1_pre_topc(A_103, B_104))=B_104 | ~m1_pre_topc(k1_pre_topc(A_103, B_104), A_103) | ~v1_pre_topc(k1_pre_topc(A_103, B_104)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.29/5.99  tff(c_733, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_272, c_723])).
% 13.29/5.99  tff(c_744, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_141, c_733])).
% 13.29/5.99  tff(c_144, plain, (![A_63, B_64]: (u1_struct_0(k1_pre_topc(A_63, B_64))=B_64 | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.29/5.99  tff(c_147, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_144])).
% 13.29/5.99  tff(c_154, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_147])).
% 13.29/5.99  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.29/5.99  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.29/5.99  tff(c_101, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 13.29/5.99  tff(c_142, plain, (![A_60]: (v1_pre_topc(k1_pre_topc(A_60, u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_101, c_131])).
% 13.29/5.99  tff(c_162, plain, (v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_142])).
% 13.29/5.99  tff(c_197, plain, (~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_162])).
% 13.29/5.99  tff(c_198, plain, (![A_66, B_67]: (m1_pre_topc(k1_pre_topc(A_66, B_67), A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.29/5.99  tff(c_204, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_198])).
% 13.29/5.99  tff(c_210, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_204])).
% 13.29/5.99  tff(c_20, plain, (![B_16, A_14]: (l1_pre_topc(B_16) | ~m1_pre_topc(B_16, A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.29/5.99  tff(c_226, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_210, c_20])).
% 13.29/5.99  tff(c_229, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_226])).
% 13.29/5.99  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_229])).
% 13.29/5.99  tff(c_233, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_162])).
% 13.29/5.99  tff(c_80, plain, (v2_compts_1('#skF_3', '#skF_2') | v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.29/5.99  tff(c_116, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_80])).
% 13.29/5.99  tff(c_28, plain, (![A_27]: (v2_compts_1(k2_struct_0(A_27), A_27) | ~v1_compts_1(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.29/5.99  tff(c_754, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_744, c_28])).
% 13.29/5.99  tff(c_762, plain, (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_116, c_754])).
% 13.29/5.99  tff(c_262, plain, (![B_73]: (m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), B_73), k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(B_73, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_154, c_256])).
% 13.29/5.99  tff(c_269, plain, (![B_73]: (m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), B_73), k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(B_73, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_262])).
% 13.29/5.99  tff(c_22, plain, (![A_17, B_19]: (u1_struct_0(k1_pre_topc(A_17, B_19))=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.29/5.99  tff(c_159, plain, (![B_19]: (u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), B_19))=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_154, c_22])).
% 13.29/5.99  tff(c_5101, plain, (![B_19]: (u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), B_19))=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_159])).
% 13.29/5.99  tff(c_308, plain, (![C_76, A_77, B_78]: (m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(B_78))) | ~m1_pre_topc(B_78, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.29/5.99  tff(c_422, plain, (![B_84, A_85]: (m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_pre_topc(B_84, A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_101, c_308])).
% 13.29/5.99  tff(c_24, plain, (![C_26, A_20, B_24]: (m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(B_24))) | ~m1_pre_topc(B_24, A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.29/5.99  tff(c_6650, plain, (![B_280, A_281, A_282]: (m1_subset_1(u1_struct_0(B_280), k1_zfmisc_1(u1_struct_0(A_281))) | ~m1_pre_topc(A_282, A_281) | ~l1_pre_topc(A_281) | ~m1_pre_topc(B_280, A_282) | ~l1_pre_topc(A_282))), inference(resolution, [status(thm)], [c_422, c_24])).
% 13.29/5.99  tff(c_6662, plain, (![B_280]: (m1_subset_1(u1_struct_0(B_280), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(B_280, k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_272, c_6650])).
% 13.29/5.99  tff(c_6675, plain, (![B_283]: (m1_subset_1(u1_struct_0(B_283), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_283, k1_pre_topc('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_40, c_6662])).
% 13.29/5.99  tff(c_13348, plain, (![B_421]: (m1_subset_1(B_421, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), B_421), k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(B_421, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5101, c_6675])).
% 13.29/5.99  tff(c_13408, plain, (![B_422]: (m1_subset_1(B_422, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_422, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_269, c_13348])).
% 13.29/5.99  tff(c_846, plain, (![A_109, B_110, C_111]: ('#skF_1'(A_109, B_110, C_111)=C_111 | v2_compts_1(C_111, A_109) | ~r1_tarski(C_111, k2_struct_0(B_110)) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_pre_topc(B_110, A_109) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.29/5.99  tff(c_854, plain, (![A_109, B_110]: ('#skF_1'(A_109, B_110, k2_struct_0(B_110))=k2_struct_0(B_110) | v2_compts_1(k2_struct_0(B_110), A_109) | ~m1_subset_1(k2_struct_0(B_110), k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_pre_topc(B_110, A_109) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_6, c_846])).
% 13.29/5.99  tff(c_13419, plain, (![B_110]: ('#skF_1'('#skF_2', B_110, k2_struct_0(B_110))=k2_struct_0(B_110) | v2_compts_1(k2_struct_0(B_110), '#skF_2') | ~m1_pre_topc(B_110, '#skF_2') | ~l1_pre_topc('#skF_2') | ~m1_subset_1(k2_struct_0(B_110), k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_13408, c_854])).
% 13.29/5.99  tff(c_25027, plain, (![B_622]: ('#skF_1'('#skF_2', B_622, k2_struct_0(B_622))=k2_struct_0(B_622) | v2_compts_1(k2_struct_0(B_622), '#skF_2') | ~m1_pre_topc(B_622, '#skF_2') | ~m1_subset_1(k2_struct_0(B_622), k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_13419])).
% 13.29/5.99  tff(c_25049, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1(k2_struct_0(k1_pre_topc('#skF_2', '#skF_3')), '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_744, c_25027])).
% 13.29/5.99  tff(c_25071, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')='#skF_3' | v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_272, c_744, c_744, c_744, c_25049])).
% 13.29/5.99  tff(c_25072, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_117, c_25071])).
% 13.29/5.99  tff(c_32, plain, (![A_28, B_40, C_46]: (~v2_compts_1('#skF_1'(A_28, B_40, C_46), B_40) | v2_compts_1(C_46, A_28) | ~r1_tarski(C_46, k2_struct_0(B_40)) | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_pre_topc(B_40, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.29/5.99  tff(c_25126, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_25072, c_32])).
% 13.29/5.99  tff(c_25176, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_272, c_38, c_6, c_744, c_762, c_25126])).
% 13.29/5.99  tff(c_25178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_25176])).
% 13.29/5.99  tff(c_25179, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 13.29/5.99  tff(c_25181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25179, c_116])).
% 13.29/5.99  tff(c_25182, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_80])).
% 13.29/5.99  tff(c_25183, plain, (~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_80])).
% 13.29/5.99  tff(c_25212, plain, (![A_630, B_631]: (u1_struct_0(k1_pre_topc(A_630, B_631))=B_631 | ~m1_subset_1(B_631, k1_zfmisc_1(u1_struct_0(A_630))) | ~l1_pre_topc(A_630))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.29/5.99  tff(c_25215, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_25212])).
% 13.29/5.99  tff(c_25222, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_25215])).
% 13.29/5.99  tff(c_25199, plain, (![A_627, B_628]: (v1_pre_topc(k1_pre_topc(A_627, B_628)) | ~m1_subset_1(B_628, k1_zfmisc_1(u1_struct_0(A_627))) | ~l1_pre_topc(A_627))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.29/5.99  tff(c_25210, plain, (![A_627]: (v1_pre_topc(k1_pre_topc(A_627, u1_struct_0(A_627))) | ~l1_pre_topc(A_627))), inference(resolution, [status(thm)], [c_101, c_25199])).
% 13.29/5.99  tff(c_25230, plain, (v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_25222, c_25210])).
% 13.29/5.99  tff(c_25265, plain, (~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_25230])).
% 13.29/5.99  tff(c_25266, plain, (![A_633, B_634]: (m1_pre_topc(k1_pre_topc(A_633, B_634), A_633) | ~m1_subset_1(B_634, k1_zfmisc_1(u1_struct_0(A_633))) | ~l1_pre_topc(A_633))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.29/5.99  tff(c_25272, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_25266])).
% 13.29/5.99  tff(c_25278, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_25272])).
% 13.29/5.99  tff(c_25282, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_25278, c_20])).
% 13.29/5.99  tff(c_25285, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_25282])).
% 13.29/5.99  tff(c_25287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25265, c_25285])).
% 13.29/5.99  tff(c_25289, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_25230])).
% 13.29/5.99  tff(c_25202, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_25199])).
% 13.29/5.99  tff(c_25209, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_25202])).
% 13.29/5.99  tff(c_25765, plain, (![A_666, B_667]: (k2_struct_0(k1_pre_topc(A_666, B_667))=B_667 | ~m1_pre_topc(k1_pre_topc(A_666, B_667), A_666) | ~v1_pre_topc(k1_pre_topc(A_666, B_667)) | ~m1_subset_1(B_667, k1_zfmisc_1(u1_struct_0(A_666))) | ~l1_pre_topc(A_666))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.29/5.99  tff(c_25775, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_25328, c_25765])).
% 13.29/5.99  tff(c_25786, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_25209, c_25775])).
% 13.29/5.99  tff(c_26, plain, (![A_27]: (v1_compts_1(A_27) | ~v2_compts_1(k2_struct_0(A_27), A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.29/5.99  tff(c_25796, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_25786, c_26])).
% 13.29/5.99  tff(c_25804, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_25289, c_25796])).
% 13.29/5.99  tff(c_25805, plain, (~v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_25183, c_25804])).
% 13.29/5.99  tff(c_26268, plain, (![D_690, B_691, A_692]: (v2_compts_1(D_690, B_691) | ~m1_subset_1(D_690, k1_zfmisc_1(u1_struct_0(B_691))) | ~v2_compts_1(D_690, A_692) | ~r1_tarski(D_690, k2_struct_0(B_691)) | ~m1_subset_1(D_690, k1_zfmisc_1(u1_struct_0(A_692))) | ~m1_pre_topc(B_691, A_692) | ~l1_pre_topc(A_692))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.29/5.99  tff(c_27119, plain, (![B_710, A_711]: (v2_compts_1(u1_struct_0(B_710), B_710) | ~v2_compts_1(u1_struct_0(B_710), A_711) | ~r1_tarski(u1_struct_0(B_710), k2_struct_0(B_710)) | ~m1_subset_1(u1_struct_0(B_710), k1_zfmisc_1(u1_struct_0(A_711))) | ~m1_pre_topc(B_710, A_711) | ~l1_pre_topc(A_711))), inference(resolution, [status(thm)], [c_101, c_26268])).
% 13.29/5.99  tff(c_27149, plain, (![A_711]: (v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), A_711) | ~r1_tarski('#skF_3', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0(A_711))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_711) | ~l1_pre_topc(A_711))), inference(superposition, [status(thm), theory('equality')], [c_25222, c_27119])).
% 13.29/5.99  tff(c_27172, plain, (![A_711]: (v2_compts_1('#skF_3', k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', A_711) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_711))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_711) | ~l1_pre_topc(A_711))), inference(demodulation, [status(thm), theory('equality')], [c_25222, c_6, c_25786, c_25222, c_25222, c_27149])).
% 13.29/5.99  tff(c_27174, plain, (![A_712]: (~v2_compts_1('#skF_3', A_712) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_712))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_712) | ~l1_pre_topc(A_712))), inference(negUnitSimplification, [status(thm)], [c_25805, c_27172])).
% 13.29/5.99  tff(c_27217, plain, (~v2_compts_1('#skF_3', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_27174])).
% 13.29/5.99  tff(c_27239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_25328, c_25182, c_27217])).
% 13.29/5.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.29/5.99  
% 13.29/5.99  Inference rules
% 13.29/5.99  ----------------------
% 13.29/5.99  #Ref     : 0
% 13.29/5.99  #Sup     : 6902
% 13.29/5.99  #Fact    : 0
% 13.29/5.99  #Define  : 0
% 13.29/5.99  #Split   : 18
% 13.29/5.99  #Chain   : 0
% 13.29/5.99  #Close   : 0
% 13.29/5.99  
% 13.29/5.99  Ordering : KBO
% 13.29/5.99  
% 13.29/5.99  Simplification rules
% 13.29/5.99  ----------------------
% 13.29/5.99  #Subsume      : 1042
% 13.29/5.99  #Demod        : 6856
% 13.29/5.99  #Tautology    : 1420
% 13.29/5.99  #SimpNegUnit  : 49
% 13.29/5.99  #BackRed      : 0
% 13.29/5.99  
% 13.29/5.99  #Partial instantiations: 0
% 13.29/5.99  #Strategies tried      : 1
% 13.29/5.99  
% 13.29/5.99  Timing (in seconds)
% 13.29/5.99  ----------------------
% 13.29/5.99  Preprocessing        : 0.34
% 13.29/5.99  Parsing              : 0.17
% 13.29/5.99  CNF conversion       : 0.03
% 13.29/5.99  Main loop            : 4.87
% 13.29/5.99  Inferencing          : 0.90
% 13.29/5.99  Reduction            : 1.46
% 13.29/5.99  Demodulation         : 1.08
% 13.29/5.99  BG Simplification    : 0.13
% 13.29/5.99  Subsumption          : 2.13
% 13.29/5.99  Abstraction          : 0.16
% 13.29/5.99  MUC search           : 0.00
% 13.29/5.99  Cooper               : 0.00
% 13.29/5.99  Total                : 5.24
% 13.29/5.99  Index Insertion      : 0.00
% 13.29/5.99  Index Deletion       : 0.00
% 13.29/5.99  Index Matching       : 0.00
% 13.29/5.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
