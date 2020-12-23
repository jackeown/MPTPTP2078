%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:22 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 324 expanded)
%              Number of leaves         :   47 ( 128 expanded)
%              Depth                    :   12
%              Number of atoms          :  184 ( 880 expanded)
%              Number of equality atoms :   17 ( 121 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k4_tarski > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v2_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc5_tops_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ~ v2_tops_1(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_74,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_97,plain,(
    ! [A_2] : r1_tarski('#skF_8',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_82,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_80,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_66,plain,(
    ! [A_41] :
      ( v4_pre_topc(k2_struct_0(A_41),A_41)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,(
    ! [A_40] :
      ( l1_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_123,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_140,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = k2_struct_0(A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_64,c_123])).

tff(c_144,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_140])).

tff(c_158,plain,(
    ! [A_72] :
      ( m1_subset_1('#skF_5'(A_72),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_161,plain,
    ( m1_subset_1('#skF_5'('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_158])).

tff(c_163,plain,(
    m1_subset_1('#skF_5'('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_161])).

tff(c_536,plain,(
    ! [C_125,B_126,A_127] :
      ( ~ v1_xboole_0(C_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(C_125))
      | ~ r2_hidden(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_545,plain,(
    ! [A_127] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_6'))
      | ~ r2_hidden(A_127,'#skF_5'('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_163,c_536])).

tff(c_579,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_146,plain,(
    m1_subset_1('#skF_7',k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_78])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_90,plain,(
    ! [D_56] :
      ( v4_pre_topc(D_56,'#skF_6')
      | ~ r2_hidden(D_56,'#skF_8')
      | ~ m1_subset_1(D_56,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_152,plain,(
    ! [D_71] :
      ( v4_pre_topc(D_71,'#skF_6')
      | ~ r2_hidden(D_71,'#skF_8')
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_90])).

tff(c_157,plain,
    ( v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6')
    | ~ r2_hidden(k2_struct_0('#skF_6'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_96,c_152])).

tff(c_530,plain,(
    ~ r2_hidden(k2_struct_0('#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_86,plain,(
    ! [D_56] :
      ( r2_hidden(D_56,'#skF_8')
      | ~ r2_hidden('#skF_7',D_56)
      | ~ v4_pre_topc(D_56,'#skF_6')
      | ~ v3_pre_topc(D_56,'#skF_6')
      | ~ m1_subset_1(D_56,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_588,plain,(
    ! [D_133] :
      ( r2_hidden(D_133,'#skF_8')
      | ~ r2_hidden('#skF_7',D_133)
      | ~ v4_pre_topc(D_133,'#skF_6')
      | ~ v3_pre_topc(D_133,'#skF_6')
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_86])).

tff(c_595,plain,
    ( r2_hidden(k2_struct_0('#skF_6'),'#skF_8')
    | ~ r2_hidden('#skF_7',k2_struct_0('#skF_6'))
    | ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6')
    | ~ v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_588])).

tff(c_601,plain,
    ( ~ r2_hidden('#skF_7',k2_struct_0('#skF_6'))
    | ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6')
    | ~ v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_595])).

tff(c_655,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_169,plain,(
    ! [A_74] :
      ( r2_hidden(u1_struct_0(A_74),u1_pre_topc(A_74))
      | ~ v2_pre_topc(A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_175,plain,
    ( r2_hidden(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_169])).

tff(c_178,plain,(
    r2_hidden(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_82,c_175])).

tff(c_736,plain,(
    ! [B_165,A_166] :
      ( v3_pre_topc(B_165,A_166)
      | ~ r2_hidden(B_165,u1_pre_topc(A_166))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_760,plain,(
    ! [A_168] :
      ( v3_pre_topc(u1_struct_0(A_168),A_168)
      | ~ r2_hidden(u1_struct_0(A_168),u1_pre_topc(A_168))
      | ~ l1_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_96,c_736])).

tff(c_769,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6')
    | ~ r2_hidden(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_760])).

tff(c_776,plain,(
    v3_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_178,c_144,c_769])).

tff(c_778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_655,c_776])).

tff(c_779,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6')
    | ~ r2_hidden('#skF_7',k2_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_782,plain,(
    ~ r2_hidden('#skF_7',k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_785,plain,
    ( v1_xboole_0(k2_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_10,c_782])).

tff(c_788,plain,(
    v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_785])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_579,c_788])).

tff(c_791,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_809,plain,
    ( ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_791])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_809])).

tff(c_815,plain,(
    v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_1] :
      ( A_1 = '#skF_8'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2])).

tff(c_820,plain,(
    k2_struct_0('#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_815,c_98])).

tff(c_72,plain,(
    ! [A_44] :
      ( ~ v2_tops_1(k2_struct_0(A_44),A_44)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_837,plain,
    ( ~ v2_tops_1('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_72])).

tff(c_844,plain,
    ( ~ v2_tops_1('#skF_8','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_837])).

tff(c_845,plain,(
    ~ v2_tops_1('#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_844])).

tff(c_16,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_95,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | A_12 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16])).

tff(c_892,plain,(
    ! [A_174] : ~ r2_hidden(A_174,'#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_902,plain,(
    '#skF_5'('#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_95,c_892])).

tff(c_68,plain,(
    ! [A_42] :
      ( v2_tops_1('#skF_5'(A_42),A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_910,plain,
    ( v2_tops_1('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_68])).

tff(c_916,plain,(
    v2_tops_1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_910])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_845,c_916])).

tff(c_920,plain,(
    r2_hidden(k2_struct_0('#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_934,plain,(
    ~ r1_tarski('#skF_8',k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_920,c_14])).

tff(c_938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.53  %$ v4_pre_topc > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k4_tarski > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_6 > #skF_8 > #skF_3
% 3.28/1.53  
% 3.28/1.53  %Foreground sorts:
% 3.28/1.53  
% 3.28/1.53  
% 3.28/1.53  %Background operators:
% 3.28/1.53  
% 3.28/1.53  
% 3.28/1.53  %Foreground operators:
% 3.28/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.28/1.53  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.28/1.53  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.28/1.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.28/1.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.28/1.53  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.28/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.28/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.28/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.53  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.28/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.28/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.28/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.28/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.28/1.53  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.28/1.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.28/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.28/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.53  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.28/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.28/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.28/1.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.28/1.53  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.28/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.53  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.28/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.53  
% 3.41/1.55  tff(f_162, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 3.41/1.55  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.41/1.55  tff(f_117, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 3.41/1.55  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.41/1.55  tff(f_98, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.41/1.55  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v2_tops_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc5_tops_1)).
% 3.41/1.55  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.41/1.55  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.41/1.55  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.41/1.55  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.41/1.55  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 3.41/1.55  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.41/1.55  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.41/1.55  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => ~v2_tops_1(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_tops_1)).
% 3.41/1.55  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.41/1.55  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.41/1.55  tff(c_74, plain, (k1_xboole_0='#skF_8'), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.41/1.55  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.41/1.55  tff(c_97, plain, (![A_2]: (r1_tarski('#skF_8', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4])).
% 3.41/1.55  tff(c_84, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.41/1.55  tff(c_82, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.41/1.55  tff(c_80, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.41/1.55  tff(c_66, plain, (![A_41]: (v4_pre_topc(k2_struct_0(A_41), A_41) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.41/1.55  tff(c_64, plain, (![A_40]: (l1_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.41/1.55  tff(c_123, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.41/1.55  tff(c_140, plain, (![A_70]: (u1_struct_0(A_70)=k2_struct_0(A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_64, c_123])).
% 3.41/1.55  tff(c_144, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_80, c_140])).
% 3.41/1.55  tff(c_158, plain, (![A_72]: (m1_subset_1('#skF_5'(A_72), k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.41/1.55  tff(c_161, plain, (m1_subset_1('#skF_5'('#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_144, c_158])).
% 3.41/1.55  tff(c_163, plain, (m1_subset_1('#skF_5'('#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_161])).
% 3.41/1.55  tff(c_536, plain, (![C_125, B_126, A_127]: (~v1_xboole_0(C_125) | ~m1_subset_1(B_126, k1_zfmisc_1(C_125)) | ~r2_hidden(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.41/1.55  tff(c_545, plain, (![A_127]: (~v1_xboole_0(k2_struct_0('#skF_6')) | ~r2_hidden(A_127, '#skF_5'('#skF_6')))), inference(resolution, [status(thm)], [c_163, c_536])).
% 3.41/1.55  tff(c_579, plain, (~v1_xboole_0(k2_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_545])).
% 3.41/1.55  tff(c_78, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.41/1.55  tff(c_146, plain, (m1_subset_1('#skF_7', k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_78])).
% 3.41/1.55  tff(c_10, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.41/1.55  tff(c_6, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.41/1.55  tff(c_8, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.41/1.55  tff(c_96, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 3.41/1.55  tff(c_90, plain, (![D_56]: (v4_pre_topc(D_56, '#skF_6') | ~r2_hidden(D_56, '#skF_8') | ~m1_subset_1(D_56, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.41/1.55  tff(c_152, plain, (![D_71]: (v4_pre_topc(D_71, '#skF_6') | ~r2_hidden(D_71, '#skF_8') | ~m1_subset_1(D_71, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_90])).
% 3.41/1.55  tff(c_157, plain, (v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6') | ~r2_hidden(k2_struct_0('#skF_6'), '#skF_8')), inference(resolution, [status(thm)], [c_96, c_152])).
% 3.41/1.55  tff(c_530, plain, (~r2_hidden(k2_struct_0('#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_157])).
% 3.41/1.55  tff(c_86, plain, (![D_56]: (r2_hidden(D_56, '#skF_8') | ~r2_hidden('#skF_7', D_56) | ~v4_pre_topc(D_56, '#skF_6') | ~v3_pre_topc(D_56, '#skF_6') | ~m1_subset_1(D_56, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.41/1.55  tff(c_588, plain, (![D_133]: (r2_hidden(D_133, '#skF_8') | ~r2_hidden('#skF_7', D_133) | ~v4_pre_topc(D_133, '#skF_6') | ~v3_pre_topc(D_133, '#skF_6') | ~m1_subset_1(D_133, k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_86])).
% 3.41/1.55  tff(c_595, plain, (r2_hidden(k2_struct_0('#skF_6'), '#skF_8') | ~r2_hidden('#skF_7', k2_struct_0('#skF_6')) | ~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6') | ~v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_96, c_588])).
% 3.41/1.55  tff(c_601, plain, (~r2_hidden('#skF_7', k2_struct_0('#skF_6')) | ~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6') | ~v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_530, c_595])).
% 3.41/1.55  tff(c_655, plain, (~v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_601])).
% 3.41/1.55  tff(c_169, plain, (![A_74]: (r2_hidden(u1_struct_0(A_74), u1_pre_topc(A_74)) | ~v2_pre_topc(A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.41/1.55  tff(c_175, plain, (r2_hidden(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_144, c_169])).
% 3.41/1.55  tff(c_178, plain, (r2_hidden(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_82, c_175])).
% 3.41/1.55  tff(c_736, plain, (![B_165, A_166]: (v3_pre_topc(B_165, A_166) | ~r2_hidden(B_165, u1_pre_topc(A_166)) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.41/1.55  tff(c_760, plain, (![A_168]: (v3_pre_topc(u1_struct_0(A_168), A_168) | ~r2_hidden(u1_struct_0(A_168), u1_pre_topc(A_168)) | ~l1_pre_topc(A_168))), inference(resolution, [status(thm)], [c_96, c_736])).
% 3.41/1.55  tff(c_769, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6') | ~r2_hidden(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_144, c_760])).
% 3.41/1.55  tff(c_776, plain, (v3_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_178, c_144, c_769])).
% 3.41/1.55  tff(c_778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_655, c_776])).
% 3.41/1.55  tff(c_779, plain, (~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6') | ~r2_hidden('#skF_7', k2_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_601])).
% 3.41/1.55  tff(c_782, plain, (~r2_hidden('#skF_7', k2_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_779])).
% 3.41/1.55  tff(c_785, plain, (v1_xboole_0(k2_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_782])).
% 3.41/1.55  tff(c_788, plain, (v1_xboole_0(k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_785])).
% 3.41/1.55  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_579, c_788])).
% 3.41/1.55  tff(c_791, plain, (~v4_pre_topc(k2_struct_0('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_779])).
% 3.41/1.55  tff(c_809, plain, (~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_66, c_791])).
% 3.41/1.55  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_809])).
% 3.41/1.55  tff(c_815, plain, (v1_xboole_0(k2_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_545])).
% 3.41/1.55  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.41/1.55  tff(c_98, plain, (![A_1]: (A_1='#skF_8' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2])).
% 3.41/1.55  tff(c_820, plain, (k2_struct_0('#skF_6')='#skF_8'), inference(resolution, [status(thm)], [c_815, c_98])).
% 3.41/1.55  tff(c_72, plain, (![A_44]: (~v2_tops_1(k2_struct_0(A_44), A_44) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.41/1.55  tff(c_837, plain, (~v2_tops_1('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_820, c_72])).
% 3.41/1.55  tff(c_844, plain, (~v2_tops_1('#skF_8', '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_837])).
% 3.41/1.55  tff(c_845, plain, (~v2_tops_1('#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_84, c_844])).
% 3.41/1.55  tff(c_16, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.41/1.55  tff(c_95, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | A_12='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16])).
% 3.41/1.55  tff(c_892, plain, (![A_174]: (~r2_hidden(A_174, '#skF_5'('#skF_6')))), inference(splitRight, [status(thm)], [c_545])).
% 3.41/1.55  tff(c_902, plain, ('#skF_5'('#skF_6')='#skF_8'), inference(resolution, [status(thm)], [c_95, c_892])).
% 3.41/1.55  tff(c_68, plain, (![A_42]: (v2_tops_1('#skF_5'(A_42), A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.41/1.55  tff(c_910, plain, (v2_tops_1('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_902, c_68])).
% 3.41/1.55  tff(c_916, plain, (v2_tops_1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_910])).
% 3.41/1.55  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_845, c_916])).
% 3.41/1.55  tff(c_920, plain, (r2_hidden(k2_struct_0('#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_157])).
% 3.41/1.55  tff(c_14, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.41/1.55  tff(c_934, plain, (~r1_tarski('#skF_8', k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_920, c_14])).
% 3.41/1.55  tff(c_938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_934])).
% 3.41/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.55  
% 3.41/1.55  Inference rules
% 3.41/1.55  ----------------------
% 3.41/1.55  #Ref     : 0
% 3.41/1.55  #Sup     : 163
% 3.41/1.55  #Fact    : 0
% 3.41/1.55  #Define  : 0
% 3.41/1.55  #Split   : 21
% 3.41/1.55  #Chain   : 0
% 3.41/1.55  #Close   : 0
% 3.41/1.55  
% 3.41/1.55  Ordering : KBO
% 3.41/1.55  
% 3.41/1.55  Simplification rules
% 3.41/1.55  ----------------------
% 3.41/1.55  #Subsume      : 26
% 3.41/1.55  #Demod        : 99
% 3.41/1.55  #Tautology    : 24
% 3.41/1.55  #SimpNegUnit  : 11
% 3.41/1.55  #BackRed      : 28
% 3.41/1.55  
% 3.41/1.55  #Partial instantiations: 0
% 3.41/1.55  #Strategies tried      : 1
% 3.41/1.55  
% 3.41/1.55  Timing (in seconds)
% 3.41/1.55  ----------------------
% 3.41/1.56  Preprocessing        : 0.36
% 3.41/1.56  Parsing              : 0.19
% 3.41/1.56  CNF conversion       : 0.03
% 3.41/1.56  Main loop            : 0.39
% 3.41/1.56  Inferencing          : 0.13
% 3.41/1.56  Reduction            : 0.12
% 3.41/1.56  Demodulation         : 0.08
% 3.41/1.56  BG Simplification    : 0.02
% 3.41/1.56  Subsumption          : 0.07
% 3.41/1.56  Abstraction          : 0.02
% 3.41/1.56  MUC search           : 0.00
% 3.41/1.56  Cooper               : 0.00
% 3.41/1.56  Total                : 0.79
% 3.41/1.56  Index Insertion      : 0.00
% 3.41/1.56  Index Deletion       : 0.00
% 3.41/1.56  Index Matching       : 0.00
% 3.41/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
