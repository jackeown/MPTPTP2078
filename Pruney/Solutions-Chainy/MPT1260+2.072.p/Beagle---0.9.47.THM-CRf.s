%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:09 EST 2020

% Result     : Theorem 10.97s
% Output     : CNFRefutation 11.06s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 489 expanded)
%              Number of leaves         :   45 ( 183 expanded)
%              Depth                    :   14
%              Number of atoms          :  222 (1044 expanded)
%              Number of equality atoms :   63 ( 246 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_64,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_123,axiom,(
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

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_128,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_563,plain,(
    ! [A_111,B_112,C_113] :
      ( k7_subset_1(A_111,B_112,C_113) = k4_xboole_0(B_112,C_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_586,plain,(
    ! [C_113] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_113) = k4_xboole_0('#skF_3',C_113) ),
    inference(resolution,[status(thm)],[c_52,c_563])).

tff(c_1290,plain,(
    ! [A_158,B_159] :
      ( k7_subset_1(u1_struct_0(A_158),B_159,k2_tops_1(A_158,B_159)) = k1_tops_1(A_158,B_159)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1320,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1290])).

tff(c_1341,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_586,c_1320])).

tff(c_40,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k2_tops_1(A_37,B_38),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1459,plain,(
    ! [A_160,B_161] :
      ( k4_subset_1(u1_struct_0(A_160),B_161,k2_tops_1(A_160,B_161)) = k2_pre_topc(A_160,B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1489,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1459])).

tff(c_1507,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1489])).

tff(c_1198,plain,(
    ! [A_150,B_151,C_152] :
      ( m1_subset_1(k4_subset_1(A_150,B_151,C_152),k1_zfmisc_1(A_150))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(A_150))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(A_150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2135,plain,(
    ! [A_190,B_191,C_192] :
      ( r1_tarski(k4_subset_1(A_190,B_191,C_192),A_190)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(A_190))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_190)) ) ),
    inference(resolution,[status(thm)],[c_1198,c_34])).

tff(c_2145,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_2135])).

tff(c_2150,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2145])).

tff(c_2152,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2150])).

tff(c_2155,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_2152])).

tff(c_2162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2155])).

tff(c_2163,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2150])).

tff(c_36,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(A_32,k1_zfmisc_1(B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_584,plain,(
    ! [B_33,A_32,C_113] :
      ( k7_subset_1(B_33,A_32,C_113) = k4_xboole_0(A_32,C_113)
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_36,c_563])).

tff(c_2666,plain,(
    ! [C_201] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_201) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_201) ),
    inference(resolution,[status(thm)],[c_2163,c_584])).

tff(c_44,plain,(
    ! [A_41,B_43] :
      ( k7_subset_1(u1_struct_0(A_41),k2_pre_topc(A_41,B_43),k1_tops_1(A_41,B_43)) = k2_tops_1(A_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2673,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2666,c_44])).

tff(c_2689,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2673])).

tff(c_749,plain,(
    ! [B_125,A_126] :
      ( r1_tarski(B_125,k2_pre_topc(A_126,B_125))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_774,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_749])).

tff(c_790,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_774])).

tff(c_64,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_81,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_2676,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2666,c_81])).

tff(c_162,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(A_84,B_85) = k3_subset_1(A_84,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,(
    ! [B_33,A_32] :
      ( k4_xboole_0(B_33,A_32) = k3_subset_1(B_33,A_32)
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_36,c_162])).

tff(c_797,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_790,c_175])).

tff(c_2693,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2676,c_797])).

tff(c_236,plain,(
    ! [A_89,B_90] :
      ( k3_subset_1(A_89,k3_subset_1(A_89,B_90)) = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_251,plain,(
    ! [B_33,A_32] :
      ( k3_subset_1(B_33,k3_subset_1(B_33,A_32)) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_36,c_236])).

tff(c_2761,plain,
    ( k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2693,c_251])).

tff(c_2771,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_2761])).

tff(c_879,plain,(
    ! [B_130,A_131,C_132] :
      ( k7_subset_1(B_130,A_131,C_132) = k4_xboole_0(A_131,C_132)
      | ~ r1_tarski(A_131,B_130) ) ),
    inference(resolution,[status(thm)],[c_36,c_563])).

tff(c_909,plain,(
    ! [C_132] : k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3',C_132) = k4_xboole_0('#skF_3',C_132) ),
    inference(resolution,[status(thm)],[c_790,c_879])).

tff(c_26,plain,(
    ! [A_21,B_22] : k6_subset_1(A_21,B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_12,B_13] : m1_subset_1(k6_subset_1(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [A_12,B_13] : m1_subset_1(k4_xboole_0(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_16])).

tff(c_486,plain,(
    ! [A_107,B_108] : k4_xboole_0(A_107,k4_xboole_0(A_107,B_108)) = k3_subset_1(A_107,k4_xboole_0(A_107,B_108)) ),
    inference(resolution,[status(thm)],[c_65,c_162])).

tff(c_501,plain,(
    ! [A_107,B_108] : m1_subset_1(k3_subset_1(A_107,k4_xboole_0(A_107,B_108)),k1_zfmisc_1(A_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_65])).

tff(c_138,plain,(
    ! [A_79,B_80,C_81] :
      ( k9_subset_1(A_79,B_80,B_80) = B_80
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_148,plain,(
    ! [A_12,B_80] : k9_subset_1(A_12,B_80,B_80) = B_80 ),
    inference(resolution,[status(thm)],[c_65,c_138])).

tff(c_1604,plain,(
    ! [A_163,B_164,C_165] :
      ( k9_subset_1(A_163,B_164,k3_subset_1(A_163,C_165)) = k7_subset_1(A_163,B_164,C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(A_163))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(A_163)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5640,plain,(
    ! [A_259,B_260,B_261] :
      ( k9_subset_1(A_259,B_260,k3_subset_1(A_259,k4_xboole_0(A_259,B_261))) = k7_subset_1(A_259,B_260,k4_xboole_0(A_259,B_261))
      | ~ m1_subset_1(B_260,k1_zfmisc_1(A_259)) ) ),
    inference(resolution,[status(thm)],[c_65,c_1604])).

tff(c_5739,plain,(
    ! [A_12,B_261] :
      ( k7_subset_1(A_12,k3_subset_1(A_12,k4_xboole_0(A_12,B_261)),k4_xboole_0(A_12,B_261)) = k3_subset_1(A_12,k4_xboole_0(A_12,B_261))
      | ~ m1_subset_1(k3_subset_1(A_12,k4_xboole_0(A_12,B_261)),k1_zfmisc_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_5640])).

tff(c_14437,plain,(
    ! [A_393,B_394] : k7_subset_1(A_393,k3_subset_1(A_393,k4_xboole_0(A_393,B_394)),k4_xboole_0(A_393,B_394)) = k3_subset_1(A_393,k4_xboole_0(A_393,B_394)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_5739])).

tff(c_14592,plain,(
    k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')),k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3'))) = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),k1_tops_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2689,c_14437])).

tff(c_14738,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_2689,c_2771,c_2689,c_909,c_2771,c_14592])).

tff(c_91,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_105,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(resolution,[status(thm)],[c_65,c_91])).

tff(c_1365,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1341,c_105])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1385,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1365,c_2])).

tff(c_1426,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1385])).

tff(c_14791,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14738,c_1426])).

tff(c_14814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14791])).

tff(c_14815,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1385])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_931,plain,(
    ! [A_134,B_135] :
      ( v3_pre_topc(k1_tops_1(A_134,B_135),A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_956,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_931])).

tff(c_972,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_956])).

tff(c_14822,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14815,c_972])).

tff(c_14828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_14822])).

tff(c_14829,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_15137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14829,c_81])).

tff(c_15138,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_15187,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15138,c_58])).

tff(c_15444,plain,(
    ! [A_456,B_457,C_458] :
      ( k7_subset_1(A_456,B_457,C_458) = k4_xboole_0(B_457,C_458)
      | ~ m1_subset_1(B_457,k1_zfmisc_1(A_456)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_15464,plain,(
    ! [C_458] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_458) = k4_xboole_0('#skF_3',C_458) ),
    inference(resolution,[status(thm)],[c_52,c_15444])).

tff(c_16405,plain,(
    ! [A_512,B_513] :
      ( k7_subset_1(u1_struct_0(A_512),B_513,k2_tops_1(A_512,B_513)) = k1_tops_1(A_512,B_513)
      | ~ m1_subset_1(B_513,k1_zfmisc_1(u1_struct_0(A_512)))
      | ~ l1_pre_topc(A_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_16435,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_16405])).

tff(c_16456,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_15464,c_16435])).

tff(c_15149,plain,(
    ! [A_423,B_424] :
      ( r1_tarski(A_423,B_424)
      | ~ m1_subset_1(A_423,k1_zfmisc_1(B_424)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_15163,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(resolution,[status(thm)],[c_65,c_15149])).

tff(c_16483,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16456,c_15163])).

tff(c_16504,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16483,c_2])).

tff(c_16545,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_16504])).

tff(c_16849,plain,(
    ! [B_523,A_524,C_525] :
      ( r1_tarski(B_523,k1_tops_1(A_524,C_525))
      | ~ r1_tarski(B_523,C_525)
      | ~ v3_pre_topc(B_523,A_524)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ m1_subset_1(B_523,k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ l1_pre_topc(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16879,plain,(
    ! [B_523] :
      ( r1_tarski(B_523,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_523,'#skF_3')
      | ~ v3_pre_topc(B_523,'#skF_2')
      | ~ m1_subset_1(B_523,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_16849])).

tff(c_17002,plain,(
    ! [B_532] :
      ( r1_tarski(B_532,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_532,'#skF_3')
      | ~ v3_pre_topc(B_532,'#skF_2')
      | ~ m1_subset_1(B_532,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16879])).

tff(c_17044,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_17002])).

tff(c_17063,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15138,c_6,c_17044])).

tff(c_17065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16545,c_17063])).

tff(c_17066,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_16504])).

tff(c_17241,plain,(
    ! [A_537,B_538] :
      ( k7_subset_1(u1_struct_0(A_537),k2_pre_topc(A_537,B_538),k1_tops_1(A_537,B_538)) = k2_tops_1(A_537,B_538)
      | ~ m1_subset_1(B_538,k1_zfmisc_1(u1_struct_0(A_537)))
      | ~ l1_pre_topc(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_17250,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17066,c_17241])).

tff(c_17254,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_17250])).

tff(c_17256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15187,c_17254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.97/4.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.97/4.25  
% 10.97/4.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.97/4.25  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3
% 10.97/4.25  
% 10.97/4.25  %Foreground sorts:
% 10.97/4.25  
% 10.97/4.25  
% 10.97/4.25  %Background operators:
% 10.97/4.25  
% 10.97/4.25  
% 10.97/4.25  %Foreground operators:
% 10.97/4.25  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.97/4.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.97/4.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.97/4.25  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.97/4.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.97/4.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.97/4.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.97/4.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.97/4.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.97/4.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.97/4.25  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.97/4.25  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.97/4.25  tff('#skF_2', type, '#skF_2': $i).
% 10.97/4.25  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.97/4.25  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 10.97/4.25  tff('#skF_3', type, '#skF_3': $i).
% 10.97/4.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.97/4.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.97/4.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.97/4.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.97/4.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.97/4.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.97/4.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.97/4.25  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.97/4.25  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.97/4.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.97/4.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.97/4.25  
% 11.06/4.27  tff(f_149, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 11.06/4.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.06/4.27  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.06/4.27  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 11.06/4.27  tff(f_94, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 11.06/4.27  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 11.06/4.27  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 11.06/4.27  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.06/4.27  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 11.06/4.27  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 11.06/4.27  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.06/4.27  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.06/4.27  tff(f_64, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.06/4.27  tff(f_49, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 11.06/4.27  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 11.06/4.27  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 11.06/4.27  tff(f_102, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 11.06/4.27  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 11.06/4.27  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.06/4.27  tff(c_128, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 11.06/4.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.06/4.27  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.06/4.27  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.06/4.27  tff(c_563, plain, (![A_111, B_112, C_113]: (k7_subset_1(A_111, B_112, C_113)=k4_xboole_0(B_112, C_113) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.06/4.27  tff(c_586, plain, (![C_113]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_113)=k4_xboole_0('#skF_3', C_113))), inference(resolution, [status(thm)], [c_52, c_563])).
% 11.06/4.27  tff(c_1290, plain, (![A_158, B_159]: (k7_subset_1(u1_struct_0(A_158), B_159, k2_tops_1(A_158, B_159))=k1_tops_1(A_158, B_159) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.06/4.27  tff(c_1320, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1290])).
% 11.06/4.27  tff(c_1341, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_586, c_1320])).
% 11.06/4.27  tff(c_40, plain, (![A_37, B_38]: (m1_subset_1(k2_tops_1(A_37, B_38), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.06/4.27  tff(c_1459, plain, (![A_160, B_161]: (k4_subset_1(u1_struct_0(A_160), B_161, k2_tops_1(A_160, B_161))=k2_pre_topc(A_160, B_161) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.06/4.27  tff(c_1489, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1459])).
% 11.06/4.27  tff(c_1507, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1489])).
% 11.06/4.27  tff(c_1198, plain, (![A_150, B_151, C_152]: (m1_subset_1(k4_subset_1(A_150, B_151, C_152), k1_zfmisc_1(A_150)) | ~m1_subset_1(C_152, k1_zfmisc_1(A_150)) | ~m1_subset_1(B_151, k1_zfmisc_1(A_150)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.06/4.27  tff(c_34, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.06/4.27  tff(c_2135, plain, (![A_190, B_191, C_192]: (r1_tarski(k4_subset_1(A_190, B_191, C_192), A_190) | ~m1_subset_1(C_192, k1_zfmisc_1(A_190)) | ~m1_subset_1(B_191, k1_zfmisc_1(A_190)))), inference(resolution, [status(thm)], [c_1198, c_34])).
% 11.06/4.27  tff(c_2145, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1507, c_2135])).
% 11.06/4.27  tff(c_2150, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2145])).
% 11.06/4.27  tff(c_2152, plain, (~m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_2150])).
% 11.06/4.27  tff(c_2155, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_2152])).
% 11.06/4.27  tff(c_2162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2155])).
% 11.06/4.27  tff(c_2163, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2150])).
% 11.06/4.27  tff(c_36, plain, (![A_32, B_33]: (m1_subset_1(A_32, k1_zfmisc_1(B_33)) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.06/4.27  tff(c_584, plain, (![B_33, A_32, C_113]: (k7_subset_1(B_33, A_32, C_113)=k4_xboole_0(A_32, C_113) | ~r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_36, c_563])).
% 11.06/4.27  tff(c_2666, plain, (![C_201]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_201)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_201))), inference(resolution, [status(thm)], [c_2163, c_584])).
% 11.06/4.27  tff(c_44, plain, (![A_41, B_43]: (k7_subset_1(u1_struct_0(A_41), k2_pre_topc(A_41, B_43), k1_tops_1(A_41, B_43))=k2_tops_1(A_41, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.06/4.27  tff(c_2673, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2666, c_44])).
% 11.06/4.27  tff(c_2689, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2673])).
% 11.06/4.27  tff(c_749, plain, (![B_125, A_126]: (r1_tarski(B_125, k2_pre_topc(A_126, B_125)) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.06/4.27  tff(c_774, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_749])).
% 11.06/4.27  tff(c_790, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_774])).
% 11.06/4.27  tff(c_64, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.06/4.27  tff(c_81, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 11.06/4.27  tff(c_2676, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2666, c_81])).
% 11.06/4.27  tff(c_162, plain, (![A_84, B_85]: (k4_xboole_0(A_84, B_85)=k3_subset_1(A_84, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.06/4.27  tff(c_175, plain, (![B_33, A_32]: (k4_xboole_0(B_33, A_32)=k3_subset_1(B_33, A_32) | ~r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_36, c_162])).
% 11.06/4.27  tff(c_797, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_790, c_175])).
% 11.06/4.27  tff(c_2693, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2676, c_797])).
% 11.06/4.27  tff(c_236, plain, (![A_89, B_90]: (k3_subset_1(A_89, k3_subset_1(A_89, B_90))=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.06/4.27  tff(c_251, plain, (![B_33, A_32]: (k3_subset_1(B_33, k3_subset_1(B_33, A_32))=A_32 | ~r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_36, c_236])).
% 11.06/4.27  tff(c_2761, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2693, c_251])).
% 11.06/4.27  tff(c_2771, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_790, c_2761])).
% 11.06/4.27  tff(c_879, plain, (![B_130, A_131, C_132]: (k7_subset_1(B_130, A_131, C_132)=k4_xboole_0(A_131, C_132) | ~r1_tarski(A_131, B_130))), inference(resolution, [status(thm)], [c_36, c_563])).
% 11.06/4.27  tff(c_909, plain, (![C_132]: (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3', C_132)=k4_xboole_0('#skF_3', C_132))), inference(resolution, [status(thm)], [c_790, c_879])).
% 11.06/4.27  tff(c_26, plain, (![A_21, B_22]: (k6_subset_1(A_21, B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.06/4.27  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k6_subset_1(A_12, B_13), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.06/4.27  tff(c_65, plain, (![A_12, B_13]: (m1_subset_1(k4_xboole_0(A_12, B_13), k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_16])).
% 11.06/4.27  tff(c_486, plain, (![A_107, B_108]: (k4_xboole_0(A_107, k4_xboole_0(A_107, B_108))=k3_subset_1(A_107, k4_xboole_0(A_107, B_108)))), inference(resolution, [status(thm)], [c_65, c_162])).
% 11.06/4.27  tff(c_501, plain, (![A_107, B_108]: (m1_subset_1(k3_subset_1(A_107, k4_xboole_0(A_107, B_108)), k1_zfmisc_1(A_107)))), inference(superposition, [status(thm), theory('equality')], [c_486, c_65])).
% 11.06/4.27  tff(c_138, plain, (![A_79, B_80, C_81]: (k9_subset_1(A_79, B_80, B_80)=B_80 | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.06/4.27  tff(c_148, plain, (![A_12, B_80]: (k9_subset_1(A_12, B_80, B_80)=B_80)), inference(resolution, [status(thm)], [c_65, c_138])).
% 11.06/4.27  tff(c_1604, plain, (![A_163, B_164, C_165]: (k9_subset_1(A_163, B_164, k3_subset_1(A_163, C_165))=k7_subset_1(A_163, B_164, C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(A_163)) | ~m1_subset_1(B_164, k1_zfmisc_1(A_163)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.06/4.27  tff(c_5640, plain, (![A_259, B_260, B_261]: (k9_subset_1(A_259, B_260, k3_subset_1(A_259, k4_xboole_0(A_259, B_261)))=k7_subset_1(A_259, B_260, k4_xboole_0(A_259, B_261)) | ~m1_subset_1(B_260, k1_zfmisc_1(A_259)))), inference(resolution, [status(thm)], [c_65, c_1604])).
% 11.06/4.27  tff(c_5739, plain, (![A_12, B_261]: (k7_subset_1(A_12, k3_subset_1(A_12, k4_xboole_0(A_12, B_261)), k4_xboole_0(A_12, B_261))=k3_subset_1(A_12, k4_xboole_0(A_12, B_261)) | ~m1_subset_1(k3_subset_1(A_12, k4_xboole_0(A_12, B_261)), k1_zfmisc_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_148, c_5640])).
% 11.06/4.27  tff(c_14437, plain, (![A_393, B_394]: (k7_subset_1(A_393, k3_subset_1(A_393, k4_xboole_0(A_393, B_394)), k4_xboole_0(A_393, B_394))=k3_subset_1(A_393, k4_xboole_0(A_393, B_394)))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_5739])).
% 11.06/4.27  tff(c_14592, plain, (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3')), k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3')))=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), k1_tops_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2689, c_14437])).
% 11.06/4.27  tff(c_14738, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_2689, c_2771, c_2689, c_909, c_2771, c_14592])).
% 11.06/4.27  tff(c_91, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.06/4.27  tff(c_105, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(resolution, [status(thm)], [c_65, c_91])).
% 11.06/4.27  tff(c_1365, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1341, c_105])).
% 11.06/4.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.06/4.27  tff(c_1385, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1365, c_2])).
% 11.06/4.27  tff(c_1426, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1385])).
% 11.06/4.27  tff(c_14791, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14738, c_1426])).
% 11.06/4.27  tff(c_14814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14791])).
% 11.06/4.27  tff(c_14815, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1385])).
% 11.06/4.27  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.06/4.27  tff(c_931, plain, (![A_134, B_135]: (v3_pre_topc(k1_tops_1(A_134, B_135), A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.06/4.27  tff(c_956, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_931])).
% 11.06/4.27  tff(c_972, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_956])).
% 11.06/4.27  tff(c_14822, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14815, c_972])).
% 11.06/4.27  tff(c_14828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_14822])).
% 11.06/4.27  tff(c_14829, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 11.06/4.27  tff(c_15137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14829, c_81])).
% 11.06/4.27  tff(c_15138, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 11.06/4.27  tff(c_15187, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15138, c_58])).
% 11.06/4.27  tff(c_15444, plain, (![A_456, B_457, C_458]: (k7_subset_1(A_456, B_457, C_458)=k4_xboole_0(B_457, C_458) | ~m1_subset_1(B_457, k1_zfmisc_1(A_456)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.06/4.27  tff(c_15464, plain, (![C_458]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_458)=k4_xboole_0('#skF_3', C_458))), inference(resolution, [status(thm)], [c_52, c_15444])).
% 11.06/4.27  tff(c_16405, plain, (![A_512, B_513]: (k7_subset_1(u1_struct_0(A_512), B_513, k2_tops_1(A_512, B_513))=k1_tops_1(A_512, B_513) | ~m1_subset_1(B_513, k1_zfmisc_1(u1_struct_0(A_512))) | ~l1_pre_topc(A_512))), inference(cnfTransformation, [status(thm)], [f_137])).
% 11.06/4.27  tff(c_16435, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_16405])).
% 11.06/4.27  tff(c_16456, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_15464, c_16435])).
% 11.06/4.27  tff(c_15149, plain, (![A_423, B_424]: (r1_tarski(A_423, B_424) | ~m1_subset_1(A_423, k1_zfmisc_1(B_424)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.06/4.27  tff(c_15163, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(resolution, [status(thm)], [c_65, c_15149])).
% 11.06/4.27  tff(c_16483, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16456, c_15163])).
% 11.06/4.27  tff(c_16504, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16483, c_2])).
% 11.06/4.27  tff(c_16545, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_16504])).
% 11.06/4.27  tff(c_16849, plain, (![B_523, A_524, C_525]: (r1_tarski(B_523, k1_tops_1(A_524, C_525)) | ~r1_tarski(B_523, C_525) | ~v3_pre_topc(B_523, A_524) | ~m1_subset_1(C_525, k1_zfmisc_1(u1_struct_0(A_524))) | ~m1_subset_1(B_523, k1_zfmisc_1(u1_struct_0(A_524))) | ~l1_pre_topc(A_524))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.06/4.27  tff(c_16879, plain, (![B_523]: (r1_tarski(B_523, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_523, '#skF_3') | ~v3_pre_topc(B_523, '#skF_2') | ~m1_subset_1(B_523, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_16849])).
% 11.06/4.27  tff(c_17002, plain, (![B_532]: (r1_tarski(B_532, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_532, '#skF_3') | ~v3_pre_topc(B_532, '#skF_2') | ~m1_subset_1(B_532, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16879])).
% 11.06/4.27  tff(c_17044, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_17002])).
% 11.06/4.27  tff(c_17063, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15138, c_6, c_17044])).
% 11.06/4.27  tff(c_17065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16545, c_17063])).
% 11.06/4.27  tff(c_17066, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_16504])).
% 11.06/4.27  tff(c_17241, plain, (![A_537, B_538]: (k7_subset_1(u1_struct_0(A_537), k2_pre_topc(A_537, B_538), k1_tops_1(A_537, B_538))=k2_tops_1(A_537, B_538) | ~m1_subset_1(B_538, k1_zfmisc_1(u1_struct_0(A_537))) | ~l1_pre_topc(A_537))), inference(cnfTransformation, [status(thm)], [f_109])).
% 11.06/4.27  tff(c_17250, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17066, c_17241])).
% 11.06/4.27  tff(c_17254, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_17250])).
% 11.06/4.27  tff(c_17256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15187, c_17254])).
% 11.06/4.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.06/4.27  
% 11.06/4.27  Inference rules
% 11.06/4.27  ----------------------
% 11.06/4.27  #Ref     : 0
% 11.06/4.27  #Sup     : 4157
% 11.06/4.27  #Fact    : 0
% 11.06/4.27  #Define  : 0
% 11.06/4.27  #Split   : 20
% 11.06/4.27  #Chain   : 0
% 11.06/4.27  #Close   : 0
% 11.06/4.27  
% 11.06/4.27  Ordering : KBO
% 11.06/4.27  
% 11.06/4.27  Simplification rules
% 11.06/4.27  ----------------------
% 11.06/4.27  #Subsume      : 246
% 11.06/4.27  #Demod        : 4289
% 11.06/4.27  #Tautology    : 1678
% 11.06/4.27  #SimpNegUnit  : 7
% 11.06/4.27  #BackRed      : 47
% 11.06/4.27  
% 11.06/4.27  #Partial instantiations: 0
% 11.06/4.27  #Strategies tried      : 1
% 11.06/4.27  
% 11.06/4.27  Timing (in seconds)
% 11.06/4.27  ----------------------
% 11.06/4.27  Preprocessing        : 0.36
% 11.06/4.27  Parsing              : 0.19
% 11.06/4.27  CNF conversion       : 0.02
% 11.06/4.27  Main loop            : 3.14
% 11.06/4.27  Inferencing          : 0.74
% 11.06/4.27  Reduction            : 1.50
% 11.06/4.27  Demodulation         : 1.24
% 11.06/4.27  BG Simplification    : 0.09
% 11.06/4.27  Subsumption          : 0.61
% 11.06/4.27  Abstraction          : 0.16
% 11.06/4.27  MUC search           : 0.00
% 11.06/4.27  Cooper               : 0.00
% 11.06/4.27  Total                : 3.54
% 11.06/4.27  Index Insertion      : 0.00
% 11.06/4.27  Index Deletion       : 0.00
% 11.06/4.27  Index Matching       : 0.00
% 11.06/4.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
