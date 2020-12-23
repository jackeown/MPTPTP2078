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
% DateTime   : Thu Dec  3 10:22:27 EST 2020

% Result     : Theorem 14.68s
% Output     : CNFRefutation 14.73s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 919 expanded)
%              Number of leaves         :   35 ( 331 expanded)
%              Depth                    :   22
%              Number of atoms          :  285 (2742 expanded)
%              Number of equality atoms :   40 ( 420 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tops_1 > v4_pre_topc > v3_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_tops_1(B,A)
             => k1_tops_1(A,k2_tops_1(A,B)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tops_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_150,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => v3_tops_1(k2_tops_1(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => ( v3_tops_1(B,A)
            <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,k2_tops_1(A,k2_tops_1(A,B))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

tff(c_44,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_76,plain,(
    ! [A_51,B_52] :
      ( v4_pre_topc(k2_pre_topc(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_76])).

tff(c_84,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_80])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(B_47,k2_pre_topc(A_48,B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_64,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_62])).

tff(c_67,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64])).

tff(c_46,plain,(
    v4_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_16,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k1_tops_1(A_8,k2_pre_topc(A_8,B_10)),B_10)
      | ~ v4_tops_1(B_10,A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k1_tops_1(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_114,plain,(
    ! [A_59,B_60] :
      ( k1_tops_1(A_59,k1_tops_1(A_59,B_60)) = k1_tops_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4122,plain,(
    ! [A_138,B_139] :
      ( k1_tops_1(A_138,k1_tops_1(A_138,k2_pre_topc(A_138,B_139))) = k1_tops_1(A_138,k2_pre_topc(A_138,B_139))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_8,c_114])).

tff(c_4136,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_4122])).

tff(c_4151,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4136])).

tff(c_81,plain,(
    ! [A_11,B_12] :
      ( v4_pre_topc(k2_pre_topc(A_11,k1_tops_1(A_11,B_12)),A_11)
      | ~ v2_pre_topc(A_11)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_4158,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4151,c_81])).

tff(c_4179,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_4158])).

tff(c_4304,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4179])).

tff(c_4308,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_4304])).

tff(c_4311,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4308])).

tff(c_4314,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_4311])).

tff(c_4318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4314])).

tff(c_4320,plain,(
    m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_4179])).

tff(c_4479,plain,(
    ! [A_144,B_145,C_146] :
      ( r1_tarski(k1_tops_1(A_144,B_145),k1_tops_1(A_144,C_146))
      | ~ r1_tarski(B_145,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4502,plain,(
    ! [C_146] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1',C_146))
      | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4151,c_4479])).

tff(c_4550,plain,(
    ! [C_146] :
      ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1',C_146))
      | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4320,c_4502])).

tff(c_122,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_114])).

tff(c_128,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_122])).

tff(c_85,plain,(
    ! [A_53,B_54] :
      ( v4_pre_topc(k2_tops_1(A_53,B_54),A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_153,plain,(
    ! [A_65,B_66] :
      ( v4_pre_topc(k2_tops_1(A_65,k1_tops_1(A_65,B_66)),A_65)
      | ~ v2_pre_topc(A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_18,c_85])).

tff(c_156,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_153])).

tff(c_158,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_156])).

tff(c_159,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_162,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_159])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_162])).

tff(c_168,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_4535,plain,(
    ! [B_145] :
      ( r1_tarski(k1_tops_1('#skF_1',B_145),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_145,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_4479])).

tff(c_4572,plain,(
    ! [B_145] :
      ( r1_tarski(k1_tops_1('#skF_1',B_145),k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_145,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_168,c_4535])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9040,plain,(
    ! [A_197,C_198,B_199] :
      ( k1_tops_1(A_197,C_198) = k1_tops_1(A_197,B_199)
      | ~ r1_tarski(k1_tops_1(A_197,C_198),k1_tops_1(A_197,B_199))
      | ~ r1_tarski(B_199,C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197) ) ),
    inference(resolution,[status(thm)],[c_4479,c_2])).

tff(c_9169,plain,(
    ! [B_145] :
      ( k1_tops_1('#skF_1',B_145) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski('#skF_2',B_145)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(B_145,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_4572,c_9040])).

tff(c_9626,plain,(
    ! [B_203] :
      ( k1_tops_1('#skF_1',B_203) = k1_tops_1('#skF_1','#skF_2')
      | ~ r1_tarski('#skF_2',B_203)
      | ~ r1_tarski(B_203,k1_tops_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_9169])).

tff(c_9647,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4320,c_9626])).

tff(c_9684,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4151,c_9647])).

tff(c_28079,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_9684])).

tff(c_28082,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4550,c_28079])).

tff(c_28091,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_28082])).

tff(c_28098,plain,
    ( ~ v4_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_28091])).

tff(c_28102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_28098])).

tff(c_28104,plain,(
    r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_9684])).

tff(c_4536,plain,(
    ! [A_144,C_146,B_145] :
      ( k1_tops_1(A_144,C_146) = k1_tops_1(A_144,B_145)
      | ~ r1_tarski(k1_tops_1(A_144,C_146),k1_tops_1(A_144,B_145))
      | ~ r1_tarski(B_145,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(resolution,[status(thm)],[c_4479,c_2])).

tff(c_28112,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28104,c_4536])).

tff(c_28119,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_67,c_28112])).

tff(c_28142,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_28119])).

tff(c_28146,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_28142])).

tff(c_28150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_28146])).

tff(c_28151,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28119])).

tff(c_4373,plain,(
    ! [A_142,B_143] :
      ( k7_subset_1(u1_struct_0(A_142),B_143,k1_tops_1(A_142,B_143)) = k2_tops_1(A_142,B_143)
      | ~ v4_pre_topc(B_143,A_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4405,plain,(
    ! [A_3,B_4] :
      ( k7_subset_1(u1_struct_0(A_3),k2_pre_topc(A_3,B_4),k1_tops_1(A_3,k2_pre_topc(A_3,B_4))) = k2_tops_1(A_3,k2_pre_topc(A_3,B_4))
      | ~ v4_pre_topc(k2_pre_topc(A_3,B_4),A_3)
      | ~ v2_pre_topc(A_3)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_4373])).

tff(c_28427,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28151,c_4405])).

tff(c_28573,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_52,c_84,c_28427])).

tff(c_26,plain,(
    ! [A_19,B_21] :
      ( k7_subset_1(u1_struct_0(A_19),k2_pre_topc(A_19,B_21),k1_tops_1(A_19,B_21)) = k2_tops_1(A_19,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30293,plain,
    ( k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28573,c_26])).

tff(c_30300,plain,(
    k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30293])).

tff(c_28152,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28119])).

tff(c_42,plain,(
    ! [A_40,B_42] :
      ( v3_tops_1(k2_tops_1(A_40,B_42),A_40)
      | ~ v4_pre_topc(B_42,A_40)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_28206,plain,
    ( v3_tops_1(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28152,c_42])).

tff(c_28264,plain,(
    v3_tops_1(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_84,c_28206])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( v4_pre_topc(k2_tops_1(A_15,B_16),A_15)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28212,plain,
    ( v4_pre_topc(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28152,c_22])).

tff(c_28273,plain,(
    v4_pre_topc(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_28212])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k2_tops_1(A_13,B_14),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_603,plain,(
    ! [A_89,B_90] :
      ( k2_tops_1(A_89,B_90) = B_90
      | ~ v3_tops_1(B_90,A_89)
      | ~ v4_pre_topc(B_90,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_634,plain,(
    ! [A_13,B_14] :
      ( k2_tops_1(A_13,k2_tops_1(A_13,B_14)) = k2_tops_1(A_13,B_14)
      | ~ v3_tops_1(k2_tops_1(A_13,B_14),A_13)
      | ~ v4_pre_topc(k2_tops_1(A_13,B_14),A_13)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_603])).

tff(c_28286,plain,
    ( k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ v3_tops_1(k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28273,c_634])).

tff(c_28291,plain,(
    k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28152,c_28264,c_28286])).

tff(c_28,plain,(
    ! [A_22,B_24] :
      ( k1_tops_1(A_22,k2_tops_1(A_22,k2_tops_1(A_22,B_24))) = k1_xboole_0
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28208,plain,
    ( k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28152,c_28])).

tff(c_28267,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_28208])).

tff(c_29166,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28291,c_28267])).

tff(c_30309,plain,(
    k1_tops_1('#skF_1',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30300,c_29166])).

tff(c_30315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_30309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.68/7.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.73/7.02  
% 14.73/7.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.73/7.02  %$ v4_tops_1 > v4_pre_topc > v3_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 14.73/7.02  
% 14.73/7.02  %Foreground sorts:
% 14.73/7.02  
% 14.73/7.02  
% 14.73/7.02  %Background operators:
% 14.73/7.02  
% 14.73/7.02  
% 14.73/7.02  %Foreground operators:
% 14.73/7.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.73/7.02  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 14.73/7.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.73/7.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.73/7.02  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 14.73/7.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.73/7.02  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 14.73/7.02  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 14.73/7.02  tff('#skF_2', type, '#skF_2': $i).
% 14.73/7.02  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.73/7.02  tff('#skF_1', type, '#skF_1': $i).
% 14.73/7.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.73/7.02  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 14.73/7.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.73/7.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.73/7.02  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.73/7.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.73/7.02  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.73/7.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.73/7.02  
% 14.73/7.04  tff(f_162, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) => (k1_tops_1(A, k2_tops_1(A, B)) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_tops_1)).
% 14.73/7.04  tff(f_83, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 14.73/7.04  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 14.73/7.04  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 14.73/7.04  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 14.73/7.04  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 14.73/7.04  tff(f_105, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 14.73/7.04  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 14.73/7.04  tff(f_75, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_tops_1)).
% 14.73/7.04  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.73/7.04  tff(f_128, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 14.73/7.04  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 14.73/7.04  tff(f_150, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_tops_1(k2_tops_1(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tops_1)).
% 14.73/7.04  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 14.73/7.04  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 14.73/7.04  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, k2_tops_1(A, k2_tops_1(A, B))) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l80_tops_1)).
% 14.73/7.04  tff(c_44, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.73/7.04  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.73/7.04  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.73/7.04  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.73/7.04  tff(c_76, plain, (![A_51, B_52]: (v4_pre_topc(k2_pre_topc(A_51, B_52), A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.73/7.04  tff(c_80, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_76])).
% 14.73/7.04  tff(c_84, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_80])).
% 14.73/7.04  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.73/7.04  tff(c_62, plain, (![B_47, A_48]: (r1_tarski(B_47, k2_pre_topc(A_48, B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.73/7.04  tff(c_64, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_62])).
% 14.73/7.04  tff(c_67, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64])).
% 14.73/7.04  tff(c_46, plain, (v4_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.73/7.04  tff(c_16, plain, (![A_8, B_10]: (r1_tarski(k1_tops_1(A_8, k2_pre_topc(A_8, B_10)), B_10) | ~v4_tops_1(B_10, A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.73/7.04  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(k1_tops_1(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.73/7.04  tff(c_114, plain, (![A_59, B_60]: (k1_tops_1(A_59, k1_tops_1(A_59, B_60))=k1_tops_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.73/7.04  tff(c_4122, plain, (![A_138, B_139]: (k1_tops_1(A_138, k1_tops_1(A_138, k2_pre_topc(A_138, B_139)))=k1_tops_1(A_138, k2_pre_topc(A_138, B_139)) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_8, c_114])).
% 14.73/7.04  tff(c_4136, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_4122])).
% 14.73/7.04  tff(c_4151, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4136])).
% 14.73/7.04  tff(c_81, plain, (![A_11, B_12]: (v4_pre_topc(k2_pre_topc(A_11, k1_tops_1(A_11, B_12)), A_11) | ~v2_pre_topc(A_11) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_18, c_76])).
% 14.73/7.04  tff(c_4158, plain, (v4_pre_topc(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4151, c_81])).
% 14.73/7.04  tff(c_4179, plain, (v4_pre_topc(k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_4158])).
% 14.73/7.04  tff(c_4304, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_4179])).
% 14.73/7.04  tff(c_4308, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_4304])).
% 14.73/7.04  tff(c_4311, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4308])).
% 14.73/7.04  tff(c_4314, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_4311])).
% 14.73/7.04  tff(c_4318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4314])).
% 14.73/7.04  tff(c_4320, plain, (m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_4179])).
% 14.73/7.04  tff(c_4479, plain, (![A_144, B_145, C_146]: (r1_tarski(k1_tops_1(A_144, B_145), k1_tops_1(A_144, C_146)) | ~r1_tarski(B_145, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_144))) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_117])).
% 14.73/7.04  tff(c_4502, plain, (![C_146]: (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', C_146)) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4151, c_4479])).
% 14.73/7.04  tff(c_4550, plain, (![C_146]: (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', C_146)) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4320, c_4502])).
% 14.73/7.04  tff(c_122, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_114])).
% 14.73/7.04  tff(c_128, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_122])).
% 14.73/7.04  tff(c_85, plain, (![A_53, B_54]: (v4_pre_topc(k2_tops_1(A_53, B_54), A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.73/7.04  tff(c_153, plain, (![A_65, B_66]: (v4_pre_topc(k2_tops_1(A_65, k1_tops_1(A_65, B_66)), A_65) | ~v2_pre_topc(A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_18, c_85])).
% 14.73/7.04  tff(c_156, plain, (v4_pre_topc(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_128, c_153])).
% 14.73/7.04  tff(c_158, plain, (v4_pre_topc(k2_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_156])).
% 14.73/7.04  tff(c_159, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_158])).
% 14.73/7.04  tff(c_162, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_159])).
% 14.73/7.04  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_162])).
% 14.73/7.04  tff(c_168, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_158])).
% 14.73/7.04  tff(c_4535, plain, (![B_145]: (r1_tarski(k1_tops_1('#skF_1', B_145), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_145, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_4479])).
% 14.73/7.04  tff(c_4572, plain, (![B_145]: (r1_tarski(k1_tops_1('#skF_1', B_145), k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_145, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_168, c_4535])).
% 14.73/7.04  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.73/7.04  tff(c_9040, plain, (![A_197, C_198, B_199]: (k1_tops_1(A_197, C_198)=k1_tops_1(A_197, B_199) | ~r1_tarski(k1_tops_1(A_197, C_198), k1_tops_1(A_197, B_199)) | ~r1_tarski(B_199, C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197))), inference(resolution, [status(thm)], [c_4479, c_2])).
% 14.73/7.04  tff(c_9169, plain, (![B_145]: (k1_tops_1('#skF_1', B_145)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', B_145) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(B_145, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_4572, c_9040])).
% 14.73/7.04  tff(c_9626, plain, (![B_203]: (k1_tops_1('#skF_1', B_203)=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', B_203) | ~r1_tarski(B_203, k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_9169])).
% 14.73/7.04  tff(c_9647, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4320, c_9626])).
% 14.73/7.04  tff(c_9684, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4151, c_9647])).
% 14.73/7.04  tff(c_28079, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_9684])).
% 14.73/7.04  tff(c_28082, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_4550, c_28079])).
% 14.73/7.04  tff(c_28091, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_28082])).
% 14.73/7.04  tff(c_28098, plain, (~v4_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_28091])).
% 14.73/7.04  tff(c_28102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_28098])).
% 14.73/7.04  tff(c_28104, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_tops_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_9684])).
% 14.73/7.04  tff(c_4536, plain, (![A_144, C_146, B_145]: (k1_tops_1(A_144, C_146)=k1_tops_1(A_144, B_145) | ~r1_tarski(k1_tops_1(A_144, C_146), k1_tops_1(A_144, B_145)) | ~r1_tarski(B_145, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_144))) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(resolution, [status(thm)], [c_4479, c_2])).
% 14.73/7.04  tff(c_28112, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28104, c_4536])).
% 14.73/7.04  tff(c_28119, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_67, c_28112])).
% 14.73/7.04  tff(c_28142, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_28119])).
% 14.73/7.04  tff(c_28146, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_28142])).
% 14.73/7.04  tff(c_28150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_28146])).
% 14.73/7.04  tff(c_28151, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_28119])).
% 14.73/7.04  tff(c_4373, plain, (![A_142, B_143]: (k7_subset_1(u1_struct_0(A_142), B_143, k1_tops_1(A_142, B_143))=k2_tops_1(A_142, B_143) | ~v4_pre_topc(B_143, A_142) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.73/7.04  tff(c_4405, plain, (![A_3, B_4]: (k7_subset_1(u1_struct_0(A_3), k2_pre_topc(A_3, B_4), k1_tops_1(A_3, k2_pre_topc(A_3, B_4)))=k2_tops_1(A_3, k2_pre_topc(A_3, B_4)) | ~v4_pre_topc(k2_pre_topc(A_3, B_4), A_3) | ~v2_pre_topc(A_3) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(resolution, [status(thm)], [c_8, c_4373])).
% 14.73/7.04  tff(c_28427, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28151, c_4405])).
% 14.73/7.04  tff(c_28573, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_52, c_84, c_28427])).
% 14.73/7.04  tff(c_26, plain, (![A_19, B_21]: (k7_subset_1(u1_struct_0(A_19), k2_pre_topc(A_19, B_21), k1_tops_1(A_19, B_21))=k2_tops_1(A_19, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.73/7.04  tff(c_30293, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28573, c_26])).
% 14.73/7.04  tff(c_30300, plain, (k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30293])).
% 14.73/7.04  tff(c_28152, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_28119])).
% 14.73/7.04  tff(c_42, plain, (![A_40, B_42]: (v3_tops_1(k2_tops_1(A_40, B_42), A_40) | ~v4_pre_topc(B_42, A_40) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_150])).
% 14.73/7.04  tff(c_28206, plain, (v3_tops_1(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28152, c_42])).
% 14.73/7.04  tff(c_28264, plain, (v3_tops_1(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_84, c_28206])).
% 14.73/7.04  tff(c_22, plain, (![A_15, B_16]: (v4_pre_topc(k2_tops_1(A_15, B_16), A_15) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.73/7.04  tff(c_28212, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28152, c_22])).
% 14.73/7.04  tff(c_28273, plain, (v4_pre_topc(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_28212])).
% 14.73/7.04  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(k2_tops_1(A_13, B_14), k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.73/7.04  tff(c_603, plain, (![A_89, B_90]: (k2_tops_1(A_89, B_90)=B_90 | ~v3_tops_1(B_90, A_89) | ~v4_pre_topc(B_90, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_139])).
% 14.73/7.04  tff(c_634, plain, (![A_13, B_14]: (k2_tops_1(A_13, k2_tops_1(A_13, B_14))=k2_tops_1(A_13, B_14) | ~v3_tops_1(k2_tops_1(A_13, B_14), A_13) | ~v4_pre_topc(k2_tops_1(A_13, B_14), A_13) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_20, c_603])).
% 14.73/7.04  tff(c_28286, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~v3_tops_1(k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28273, c_634])).
% 14.73/7.04  tff(c_28291, plain, (k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28152, c_28264, c_28286])).
% 14.73/7.04  tff(c_28, plain, (![A_22, B_24]: (k1_tops_1(A_22, k2_tops_1(A_22, k2_tops_1(A_22, B_24)))=k1_xboole_0 | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.73/7.04  tff(c_28208, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))=k1_xboole_0 | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28152, c_28])).
% 14.73/7.04  tff(c_28267, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_28208])).
% 14.73/7.04  tff(c_29166, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28291, c_28267])).
% 14.73/7.04  tff(c_30309, plain, (k1_tops_1('#skF_1', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30300, c_29166])).
% 14.73/7.04  tff(c_30315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_30309])).
% 14.73/7.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.73/7.04  
% 14.73/7.04  Inference rules
% 14.73/7.04  ----------------------
% 14.73/7.04  #Ref     : 0
% 14.73/7.04  #Sup     : 6464
% 14.73/7.04  #Fact    : 0
% 14.73/7.04  #Define  : 0
% 14.73/7.04  #Split   : 111
% 14.73/7.04  #Chain   : 0
% 14.73/7.04  #Close   : 0
% 14.73/7.04  
% 14.73/7.04  Ordering : KBO
% 14.73/7.04  
% 14.73/7.04  Simplification rules
% 14.73/7.04  ----------------------
% 14.73/7.04  #Subsume      : 936
% 14.73/7.04  #Demod        : 15875
% 14.73/7.04  #Tautology    : 2653
% 14.73/7.04  #SimpNegUnit  : 418
% 14.73/7.04  #BackRed      : 63
% 14.73/7.04  
% 14.73/7.04  #Partial instantiations: 0
% 14.73/7.04  #Strategies tried      : 1
% 14.73/7.04  
% 14.73/7.04  Timing (in seconds)
% 14.73/7.04  ----------------------
% 14.73/7.05  Preprocessing        : 0.32
% 14.73/7.05  Parsing              : 0.18
% 14.73/7.05  CNF conversion       : 0.02
% 14.73/7.05  Main loop            : 5.94
% 14.73/7.05  Inferencing          : 1.00
% 14.73/7.05  Reduction            : 3.25
% 14.73/7.05  Demodulation         : 2.73
% 14.73/7.05  BG Simplification    : 0.12
% 14.73/7.05  Subsumption          : 1.30
% 14.73/7.05  Abstraction          : 0.19
% 14.73/7.05  MUC search           : 0.00
% 14.73/7.05  Cooper               : 0.00
% 14.73/7.05  Total                : 6.31
% 14.73/7.05  Index Insertion      : 0.00
% 14.73/7.05  Index Deletion       : 0.00
% 14.73/7.05  Index Matching       : 0.00
% 14.73/7.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
