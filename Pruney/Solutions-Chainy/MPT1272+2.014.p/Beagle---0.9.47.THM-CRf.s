%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:59 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 294 expanded)
%              Number of leaves         :   31 ( 114 expanded)
%              Depth                    :   12
%              Number of atoms          :  166 ( 703 expanded)
%              Number of equality atoms :   19 (  69 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v1_tops_1(B,A)
                  & r1_tarski(B,C) )
               => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

tff(c_30,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_38,B_39] :
      ( k3_subset_1(A_38,k3_subset_1(A_38,B_39)) = B_39
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_37])).

tff(c_150,plain,(
    ! [B_54,A_55] :
      ( v2_tops_1(B_54,A_55)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_55),B_54),A_55)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_157,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_150])).

tff(c_159,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_157])).

tff(c_170,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_186,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_170])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_186])).

tff(c_192,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k2_pre_topc(A_9,B_10),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_61,plain,(
    ! [A_46,B_47] :
      ( v2_tops_1(k2_pre_topc(A_46,B_47),A_46)
      | ~ v3_tops_1(B_47,A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_70,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_76,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_70])).

tff(c_121,plain,(
    ! [A_52,B_53] :
      ( k2_pre_topc(A_52,k2_pre_topc(A_52,B_53)) = k2_pre_topc(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_130,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_121])).

tff(c_136,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_130])).

tff(c_18,plain,(
    ! [B_21,A_19] :
      ( v3_tops_1(B_21,A_19)
      | ~ v2_tops_1(k2_pre_topc(A_19,B_21),A_19)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_139,plain,
    ( v3_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_18])).

tff(c_146,plain,
    ( v3_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_76,c_139])).

tff(c_160,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_163,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_160])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_163])).

tff(c_169,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_487,plain,(
    ! [A_66,B_67] :
      ( k3_subset_1(u1_struct_0(A_66),k2_pre_topc(A_66,k3_subset_1(u1_struct_0(A_66),B_67))) = k1_tops_1(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_530,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_487])).

tff(c_540,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_192,c_530])).

tff(c_16,plain,(
    ! [A_16,B_18] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_16),B_18),A_16)
      | ~ v2_tops_1(B_18,A_16)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_569,plain,
    ( v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_16])).

tff(c_586,plain,(
    v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_169,c_76,c_569])).

tff(c_578,plain,
    ( m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_2])).

tff(c_592,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_578])).

tff(c_221,plain,(
    ! [A_56,B_57] :
      ( k2_tops_1(A_56,k3_subset_1(u1_struct_0(A_56),B_57)) = k2_tops_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_234,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_221])).

tff(c_246,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_234])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_tops_1(A_22,B_23),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_250,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_22])).

tff(c_254,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_192,c_250])).

tff(c_398,plain,(
    ! [A_60,B_61] :
      ( k4_subset_1(u1_struct_0(A_60),B_61,k2_tops_1(A_60,B_61)) = k2_pre_topc(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_413,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_398])).

tff(c_428,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_413])).

tff(c_433,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(k3_subset_1(A_62,k4_subset_1(A_62,B_63,C_64)),k3_subset_1(A_62,B_63))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_436,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_433])).

tff(c_450,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_254,c_436])).

tff(c_541,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_tops_1(C_68,A_69)
      | ~ r1_tarski(B_70,C_68)
      | ~ v1_tops_1(B_70,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_555,plain,(
    ! [A_69] :
      ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_69)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),A_69)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_450,c_541])).

tff(c_1268,plain,(
    ! [A_88] :
      ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),A_88)
      | ~ v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),A_88)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_540,c_555])).

tff(c_1271,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_1(k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_592,c_1268])).

tff(c_1274,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_192,c_586,c_1271])).

tff(c_1276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.62  
% 3.44/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.63  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.44/1.63  
% 3.44/1.63  %Foreground sorts:
% 3.44/1.63  
% 3.44/1.63  
% 3.44/1.63  %Background operators:
% 3.44/1.63  
% 3.44/1.63  
% 3.44/1.63  %Foreground operators:
% 3.44/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.63  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.44/1.63  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.44/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.44/1.63  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.44/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.44/1.63  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.44/1.63  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.44/1.63  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.44/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.44/1.63  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.44/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.63  
% 3.80/1.64  tff(f_121, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 3.80/1.64  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.80/1.64  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.80/1.64  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 3.80/1.64  tff(f_46, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.80/1.64  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 3.80/1.64  tff(f_52, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 3.80/1.64  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 3.80/1.64  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 3.80/1.64  tff(f_83, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.80/1.64  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 3.80/1.64  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 3.80/1.64  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_1)).
% 3.80/1.64  tff(c_30, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.80/1.64  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.80/1.64  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.80/1.64  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.80/1.64  tff(c_37, plain, (![A_38, B_39]: (k3_subset_1(A_38, k3_subset_1(A_38, B_39))=B_39 | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.80/1.64  tff(c_40, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_37])).
% 3.80/1.64  tff(c_150, plain, (![B_54, A_55]: (v2_tops_1(B_54, A_55) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_55), B_54), A_55) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.80/1.64  tff(c_157, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_150])).
% 3.80/1.64  tff(c_159, plain, (v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_157])).
% 3.80/1.64  tff(c_170, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_159])).
% 3.80/1.64  tff(c_186, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_170])).
% 3.80/1.64  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_186])).
% 3.80/1.64  tff(c_192, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_159])).
% 3.80/1.64  tff(c_8, plain, (![A_9, B_10]: (m1_subset_1(k2_pre_topc(A_9, B_10), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.80/1.64  tff(c_32, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.80/1.64  tff(c_61, plain, (![A_46, B_47]: (v2_tops_1(k2_pre_topc(A_46, B_47), A_46) | ~v3_tops_1(B_47, A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.80/1.64  tff(c_70, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_61])).
% 3.80/1.64  tff(c_76, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_70])).
% 3.80/1.64  tff(c_121, plain, (![A_52, B_53]: (k2_pre_topc(A_52, k2_pre_topc(A_52, B_53))=k2_pre_topc(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.80/1.64  tff(c_130, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_121])).
% 3.80/1.64  tff(c_136, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_130])).
% 3.80/1.64  tff(c_18, plain, (![B_21, A_19]: (v3_tops_1(B_21, A_19) | ~v2_tops_1(k2_pre_topc(A_19, B_21), A_19) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.80/1.64  tff(c_139, plain, (v3_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_136, c_18])).
% 3.80/1.64  tff(c_146, plain, (v3_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_76, c_139])).
% 3.80/1.64  tff(c_160, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_146])).
% 3.80/1.64  tff(c_163, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_160])).
% 3.80/1.64  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_163])).
% 3.80/1.64  tff(c_169, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_146])).
% 3.80/1.64  tff(c_487, plain, (![A_66, B_67]: (k3_subset_1(u1_struct_0(A_66), k2_pre_topc(A_66, k3_subset_1(u1_struct_0(A_66), B_67)))=k1_tops_1(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.80/1.64  tff(c_530, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_487])).
% 3.80/1.64  tff(c_540, plain, (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_192, c_530])).
% 3.80/1.64  tff(c_16, plain, (![A_16, B_18]: (v1_tops_1(k3_subset_1(u1_struct_0(A_16), B_18), A_16) | ~v2_tops_1(B_18, A_16) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.80/1.64  tff(c_569, plain, (v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_540, c_16])).
% 3.80/1.64  tff(c_586, plain, (v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_169, c_76, c_569])).
% 3.80/1.64  tff(c_578, plain, (m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_540, c_2])).
% 3.80/1.64  tff(c_592, plain, (m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_578])).
% 3.80/1.64  tff(c_221, plain, (![A_56, B_57]: (k2_tops_1(A_56, k3_subset_1(u1_struct_0(A_56), B_57))=k2_tops_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.80/1.64  tff(c_234, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_221])).
% 3.80/1.64  tff(c_246, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_234])).
% 3.80/1.64  tff(c_22, plain, (![A_22, B_23]: (m1_subset_1(k2_tops_1(A_22, B_23), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.80/1.64  tff(c_250, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_246, c_22])).
% 3.80/1.64  tff(c_254, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_192, c_250])).
% 3.80/1.64  tff(c_398, plain, (![A_60, B_61]: (k4_subset_1(u1_struct_0(A_60), B_61, k2_tops_1(A_60, B_61))=k2_pre_topc(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.80/1.64  tff(c_413, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_398])).
% 3.80/1.64  tff(c_428, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_413])).
% 3.80/1.64  tff(c_433, plain, (![A_62, B_63, C_64]: (r1_tarski(k3_subset_1(A_62, k4_subset_1(A_62, B_63, C_64)), k3_subset_1(A_62, B_63)) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.80/1.64  tff(c_436, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_428, c_433])).
% 3.80/1.64  tff(c_450, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_254, c_436])).
% 3.80/1.64  tff(c_541, plain, (![C_68, A_69, B_70]: (v1_tops_1(C_68, A_69) | ~r1_tarski(B_70, C_68) | ~v1_tops_1(B_70, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.80/1.64  tff(c_555, plain, (![A_69]: (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_69) | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), A_69) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_450, c_541])).
% 3.80/1.64  tff(c_1268, plain, (![A_88]: (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), A_88) | ~v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), A_88) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_540, c_555])).
% 3.80/1.64  tff(c_1271, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_1(k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_592, c_1268])).
% 3.80/1.64  tff(c_1274, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_192, c_586, c_1271])).
% 3.80/1.64  tff(c_1276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1274])).
% 3.80/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.64  
% 3.80/1.64  Inference rules
% 3.80/1.64  ----------------------
% 3.80/1.64  #Ref     : 0
% 3.80/1.64  #Sup     : 295
% 3.80/1.64  #Fact    : 0
% 3.80/1.64  #Define  : 0
% 3.80/1.64  #Split   : 12
% 3.80/1.64  #Chain   : 0
% 3.80/1.64  #Close   : 0
% 3.80/1.64  
% 3.80/1.64  Ordering : KBO
% 3.80/1.64  
% 3.80/1.64  Simplification rules
% 3.80/1.64  ----------------------
% 3.80/1.64  #Subsume      : 9
% 3.80/1.64  #Demod        : 297
% 3.80/1.64  #Tautology    : 130
% 3.80/1.64  #SimpNegUnit  : 4
% 3.80/1.64  #BackRed      : 3
% 3.80/1.64  
% 3.80/1.64  #Partial instantiations: 0
% 3.80/1.64  #Strategies tried      : 1
% 3.80/1.64  
% 3.80/1.64  Timing (in seconds)
% 3.80/1.64  ----------------------
% 3.80/1.65  Preprocessing        : 0.33
% 3.80/1.65  Parsing              : 0.18
% 3.80/1.65  CNF conversion       : 0.02
% 3.80/1.65  Main loop            : 0.54
% 3.80/1.65  Inferencing          : 0.19
% 3.80/1.65  Reduction            : 0.19
% 3.80/1.65  Demodulation         : 0.14
% 3.80/1.65  BG Simplification    : 0.03
% 3.80/1.65  Subsumption          : 0.11
% 3.80/1.65  Abstraction          : 0.03
% 3.80/1.65  MUC search           : 0.00
% 3.80/1.65  Cooper               : 0.00
% 3.80/1.65  Total                : 0.90
% 3.80/1.65  Index Insertion      : 0.00
% 3.80/1.65  Index Deletion       : 0.00
% 3.80/1.65  Index Matching       : 0.00
% 3.80/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
