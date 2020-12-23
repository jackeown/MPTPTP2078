%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:37 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 539 expanded)
%              Number of leaves         :   23 ( 194 expanded)
%              Depth                    :   16
%              Number of atoms          :  170 (1331 expanded)
%              Number of equality atoms :   37 ( 228 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & r1_tarski(B,C) )
                 => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_14,c_38])).

tff(c_56,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_30])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_59,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_28,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_260,plain,(
    ! [A_50,B_51] :
      ( k2_pre_topc(A_50,B_51) = k2_struct_0(A_50)
      | ~ v1_tops_1(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_267,plain,(
    ! [B_51] :
      ( k2_pre_topc('#skF_1',B_51) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_51,'#skF_1')
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_260])).

tff(c_280,plain,(
    ! [B_54] :
      ( k2_pre_topc('#skF_1',B_54) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_54,'#skF_1')
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_267])).

tff(c_286,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_59,c_280])).

tff(c_295,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_286])).

tff(c_386,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(k2_pre_topc(A_63,B_64),k2_pre_topc(A_63,C_65))
      | ~ r1_tarski(B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_397,plain,(
    ! [C_65] :
      ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',C_65))
      | ~ r1_tarski('#skF_2',C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_386])).

tff(c_413,plain,(
    ! [C_65] :
      ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',C_65))
      | ~ r1_tarski('#skF_2',C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_59,c_56,c_56,c_397])).

tff(c_24,plain,(
    ~ v1_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_99,plain,(
    ! [B_33,A_34] :
      ( v1_tops_1(B_33,A_34)
      | k2_pre_topc(A_34,B_33) != k2_struct_0(A_34)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_106,plain,(
    ! [B_33] :
      ( v1_tops_1(B_33,'#skF_1')
      | k2_pre_topc('#skF_1',B_33) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_99])).

tff(c_110,plain,(
    ! [B_35] :
      ( v1_tops_1(B_35,'#skF_1')
      | k2_pre_topc('#skF_1',B_35) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_106])).

tff(c_113,plain,
    ( v1_tops_1('#skF_3','#skF_1')
    | k2_pre_topc('#skF_1','#skF_3') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_110])).

tff(c_123,plain,(
    k2_pre_topc('#skF_1','#skF_3') != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_113])).

tff(c_43,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_43])).

tff(c_57,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_51])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [A_36] :
      ( v1_tops_1(A_36,'#skF_1')
      | k2_pre_topc('#skF_1',A_36) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_36,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_110])).

tff(c_142,plain,
    ( v1_tops_1(k2_struct_0('#skF_1'),'#skF_1')
    | k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_143,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_161,plain,(
    ! [A_40,B_41] :
      ( k2_pre_topc(A_40,B_41) = k2_struct_0(A_40)
      | ~ v1_tops_1(B_41,A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_168,plain,(
    ! [B_41] :
      ( k2_pre_topc('#skF_1',B_41) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_41,'#skF_1')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_161])).

tff(c_181,plain,(
    ! [B_44] :
      ( k2_pre_topc('#skF_1',B_44) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_44,'#skF_1')
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_168])).

tff(c_187,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_59,c_181])).

tff(c_196,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_187])).

tff(c_172,plain,(
    ! [A_42,B_43] :
      ( k2_pre_topc(A_42,k2_pre_topc(A_42,B_43)) = k2_pre_topc(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_177,plain,(
    ! [B_43] :
      ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',B_43)) = k2_pre_topc('#skF_1',B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_172])).

tff(c_221,plain,(
    ! [B_46] :
      ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',B_46)) = k2_pre_topc('#skF_1',B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_177])).

tff(c_227,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_59,c_221])).

tff(c_234,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_196,c_227])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_234])).

tff(c_238,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_406,plain,(
    ! [B_64] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_64),k2_struct_0('#skF_1'))
      | ~ r1_tarski(B_64,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_386])).

tff(c_419,plain,(
    ! [B_64] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_64),k2_struct_0('#skF_1'))
      | ~ r1_tarski(B_64,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_56,c_56,c_406])).

tff(c_871,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_874,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_871])).

tff(c_878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_874])).

tff(c_926,plain,(
    ! [B_85] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_85),k2_struct_0('#skF_1'))
      | ~ r1_tarski(B_85,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_271,plain,(
    ! [A_52,B_53] :
      ( k2_pre_topc(A_52,k2_pre_topc(A_52,B_53)) = k2_pre_topc(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_276,plain,(
    ! [B_53] :
      ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',B_53)) = k2_pre_topc('#skF_1',B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_271])).

tff(c_320,plain,(
    ! [B_56] :
      ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',B_56)) = k2_pre_topc('#skF_1',B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_276])).

tff(c_331,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = k2_pre_topc('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_320])).

tff(c_440,plain,(
    ! [C_67] :
      ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',C_67))
      | ~ r1_tarski('#skF_2',C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_59,c_56,c_56,c_397])).

tff(c_449,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_440])).

tff(c_497,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_501,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_497])).

tff(c_937,plain,
    ( ~ r1_tarski('#skF_3',k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_926,c_501])).

tff(c_971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_57,c_937])).

tff(c_973,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_993,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_3'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_973,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1004,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = k2_struct_0('#skF_1')
    | ~ r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_993,c_2])).

tff(c_1015,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1004])).

tff(c_1018,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_413,c_1015])).

tff(c_1022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_26,c_1018])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.79  
% 3.33/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.80  %$ v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.33/1.80  
% 3.33/1.80  %Foreground sorts:
% 3.33/1.80  
% 3.33/1.80  
% 3.33/1.80  %Background operators:
% 3.33/1.80  
% 3.33/1.80  
% 3.33/1.80  %Foreground operators:
% 3.33/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.80  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.33/1.80  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.80  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.80  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.80  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.33/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.80  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.33/1.80  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.33/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.80  
% 3.57/1.81  tff(f_85, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_1)).
% 3.57/1.81  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.57/1.81  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.57/1.81  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.57/1.81  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 3.57/1.81  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.57/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.57/1.81  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 3.57/1.81  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.57/1.81  tff(c_14, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.57/1.81  tff(c_38, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.57/1.81  tff(c_52, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_14, c_38])).
% 3.57/1.81  tff(c_56, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_52])).
% 3.57/1.81  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.57/1.81  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_30])).
% 3.57/1.81  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.57/1.81  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.57/1.81  tff(c_59, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32])).
% 3.57/1.81  tff(c_28, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.57/1.81  tff(c_260, plain, (![A_50, B_51]: (k2_pre_topc(A_50, B_51)=k2_struct_0(A_50) | ~v1_tops_1(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.57/1.81  tff(c_267, plain, (![B_51]: (k2_pre_topc('#skF_1', B_51)=k2_struct_0('#skF_1') | ~v1_tops_1(B_51, '#skF_1') | ~m1_subset_1(B_51, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_260])).
% 3.57/1.81  tff(c_280, plain, (![B_54]: (k2_pre_topc('#skF_1', B_54)=k2_struct_0('#skF_1') | ~v1_tops_1(B_54, '#skF_1') | ~m1_subset_1(B_54, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_267])).
% 3.57/1.81  tff(c_286, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_59, c_280])).
% 3.57/1.81  tff(c_295, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_286])).
% 3.57/1.81  tff(c_386, plain, (![A_63, B_64, C_65]: (r1_tarski(k2_pre_topc(A_63, B_64), k2_pre_topc(A_63, C_65)) | ~r1_tarski(B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.57/1.81  tff(c_397, plain, (![C_65]: (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', C_65)) | ~r1_tarski('#skF_2', C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_386])).
% 3.57/1.81  tff(c_413, plain, (![C_65]: (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', C_65)) | ~r1_tarski('#skF_2', C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_59, c_56, c_56, c_397])).
% 3.57/1.81  tff(c_24, plain, (~v1_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.57/1.81  tff(c_99, plain, (![B_33, A_34]: (v1_tops_1(B_33, A_34) | k2_pre_topc(A_34, B_33)!=k2_struct_0(A_34) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.57/1.81  tff(c_106, plain, (![B_33]: (v1_tops_1(B_33, '#skF_1') | k2_pre_topc('#skF_1', B_33)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_33, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_99])).
% 3.57/1.81  tff(c_110, plain, (![B_35]: (v1_tops_1(B_35, '#skF_1') | k2_pre_topc('#skF_1', B_35)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_35, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_106])).
% 3.57/1.81  tff(c_113, plain, (v1_tops_1('#skF_3', '#skF_1') | k2_pre_topc('#skF_1', '#skF_3')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_110])).
% 3.57/1.81  tff(c_123, plain, (k2_pre_topc('#skF_1', '#skF_3')!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_24, c_113])).
% 3.57/1.81  tff(c_43, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.81  tff(c_51, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_43])).
% 3.57/1.81  tff(c_57, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_51])).
% 3.57/1.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.81  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.81  tff(c_127, plain, (![A_36]: (v1_tops_1(A_36, '#skF_1') | k2_pre_topc('#skF_1', A_36)!=k2_struct_0('#skF_1') | ~r1_tarski(A_36, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_110])).
% 3.57/1.81  tff(c_142, plain, (v1_tops_1(k2_struct_0('#skF_1'), '#skF_1') | k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_127])).
% 3.57/1.81  tff(c_143, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_142])).
% 3.57/1.81  tff(c_161, plain, (![A_40, B_41]: (k2_pre_topc(A_40, B_41)=k2_struct_0(A_40) | ~v1_tops_1(B_41, A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.57/1.81  tff(c_168, plain, (![B_41]: (k2_pre_topc('#skF_1', B_41)=k2_struct_0('#skF_1') | ~v1_tops_1(B_41, '#skF_1') | ~m1_subset_1(B_41, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_161])).
% 3.57/1.81  tff(c_181, plain, (![B_44]: (k2_pre_topc('#skF_1', B_44)=k2_struct_0('#skF_1') | ~v1_tops_1(B_44, '#skF_1') | ~m1_subset_1(B_44, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_168])).
% 3.57/1.81  tff(c_187, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_59, c_181])).
% 3.57/1.81  tff(c_196, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_187])).
% 3.57/1.81  tff(c_172, plain, (![A_42, B_43]: (k2_pre_topc(A_42, k2_pre_topc(A_42, B_43))=k2_pre_topc(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.57/1.81  tff(c_177, plain, (![B_43]: (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', B_43))=k2_pre_topc('#skF_1', B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_172])).
% 3.57/1.81  tff(c_221, plain, (![B_46]: (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', B_46))=k2_pre_topc('#skF_1', B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_177])).
% 3.57/1.81  tff(c_227, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_59, c_221])).
% 3.57/1.81  tff(c_234, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_196, c_227])).
% 3.57/1.81  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_234])).
% 3.57/1.81  tff(c_238, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_142])).
% 3.57/1.81  tff(c_406, plain, (![B_64]: (r1_tarski(k2_pre_topc('#skF_1', B_64), k2_struct_0('#skF_1')) | ~r1_tarski(B_64, k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_386])).
% 3.57/1.81  tff(c_419, plain, (![B_64]: (r1_tarski(k2_pre_topc('#skF_1', B_64), k2_struct_0('#skF_1')) | ~r1_tarski(B_64, k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_56, c_56, c_406])).
% 3.57/1.81  tff(c_871, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_419])).
% 3.57/1.81  tff(c_874, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_871])).
% 3.57/1.81  tff(c_878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_874])).
% 3.57/1.81  tff(c_926, plain, (![B_85]: (r1_tarski(k2_pre_topc('#skF_1', B_85), k2_struct_0('#skF_1')) | ~r1_tarski(B_85, k2_struct_0('#skF_1')) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_419])).
% 3.57/1.81  tff(c_271, plain, (![A_52, B_53]: (k2_pre_topc(A_52, k2_pre_topc(A_52, B_53))=k2_pre_topc(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.57/1.81  tff(c_276, plain, (![B_53]: (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', B_53))=k2_pre_topc('#skF_1', B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_271])).
% 3.57/1.81  tff(c_320, plain, (![B_56]: (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', B_56))=k2_pre_topc('#skF_1', B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_276])).
% 3.57/1.81  tff(c_331, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))=k2_pre_topc('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_320])).
% 3.57/1.81  tff(c_440, plain, (![C_67]: (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', C_67)) | ~r1_tarski('#skF_2', C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_59, c_56, c_56, c_397])).
% 3.57/1.81  tff(c_449, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_331, c_440])).
% 3.57/1.81  tff(c_497, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_449])).
% 3.57/1.81  tff(c_501, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_497])).
% 3.57/1.81  tff(c_937, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_926, c_501])).
% 3.57/1.81  tff(c_971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_57, c_937])).
% 3.57/1.81  tff(c_973, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_449])).
% 3.57/1.81  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.81  tff(c_993, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_973, c_8])).
% 3.57/1.81  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.81  tff(c_1004, plain, (k2_pre_topc('#skF_1', '#skF_3')=k2_struct_0('#skF_1') | ~r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_993, c_2])).
% 3.57/1.81  tff(c_1015, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_123, c_1004])).
% 3.57/1.81  tff(c_1018, plain, (~r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_413, c_1015])).
% 3.57/1.81  tff(c_1022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_26, c_1018])).
% 3.57/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.81  
% 3.57/1.81  Inference rules
% 3.57/1.81  ----------------------
% 3.57/1.81  #Ref     : 0
% 3.57/1.81  #Sup     : 202
% 3.57/1.81  #Fact    : 0
% 3.57/1.81  #Define  : 0
% 3.57/1.81  #Split   : 6
% 3.57/1.81  #Chain   : 0
% 3.57/1.81  #Close   : 0
% 3.57/1.82  
% 3.57/1.82  Ordering : KBO
% 3.57/1.82  
% 3.57/1.82  Simplification rules
% 3.57/1.82  ----------------------
% 3.57/1.82  #Subsume      : 53
% 3.57/1.82  #Demod        : 306
% 3.57/1.82  #Tautology    : 61
% 3.57/1.82  #SimpNegUnit  : 18
% 3.57/1.82  #BackRed      : 4
% 3.57/1.82  
% 3.57/1.82  #Partial instantiations: 0
% 3.57/1.82  #Strategies tried      : 1
% 3.57/1.82  
% 3.57/1.82  Timing (in seconds)
% 3.57/1.82  ----------------------
% 3.57/1.82  Preprocessing        : 0.51
% 3.57/1.82  Parsing              : 0.27
% 3.57/1.82  CNF conversion       : 0.04
% 3.57/1.82  Main loop            : 0.55
% 3.57/1.82  Inferencing          : 0.19
% 3.57/1.82  Reduction            : 0.18
% 3.57/1.82  Demodulation         : 0.13
% 3.57/1.82  BG Simplification    : 0.03
% 3.57/1.82  Subsumption          : 0.11
% 3.57/1.82  Abstraction          : 0.03
% 3.57/1.82  MUC search           : 0.00
% 3.57/1.82  Cooper               : 0.00
% 3.57/1.82  Total                : 1.10
% 3.57/1.82  Index Insertion      : 0.00
% 3.57/1.82  Index Deletion       : 0.00
% 3.57/1.82  Index Matching       : 0.00
% 3.57/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
