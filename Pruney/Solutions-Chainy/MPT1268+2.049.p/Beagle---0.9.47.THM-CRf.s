%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:53 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 121 expanded)
%              Number of leaves         :   33 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 345 expanded)
%              Number of equality atoms :   23 (  53 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_64,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_139,plain,(
    ! [B_83,A_84] :
      ( v2_tops_1(B_83,A_84)
      | k1_tops_1(A_84,B_83) != k1_xboole_0
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_142,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_139])).

tff(c_145,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_142])).

tff(c_146,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_145])).

tff(c_102,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k1_tops_1(A_72,B_73),B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_104,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_102])).

tff(c_107,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_104])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_125,plain,(
    ! [A_79,B_80] :
      ( v3_pre_topc(k1_tops_1(A_79,B_80),A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_125])).

tff(c_130,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_127])).

tff(c_20,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k1_tops_1(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [C_57] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_57
      | ~ v3_pre_topc(C_57,'#skF_1')
      | ~ r1_tarski(C_57,'#skF_2')
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_172,plain,(
    ! [C_93] :
      ( k1_xboole_0 = C_93
      | ~ v3_pre_topc(C_93,'#skF_1')
      | ~ r1_tarski(C_93,'#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56])).

tff(c_176,plain,(
    ! [B_34] :
      ( k1_tops_1('#skF_1',B_34) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_34),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_34),'#skF_2')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_172])).

tff(c_210,plain,(
    ! [B_107] :
      ( k1_tops_1('#skF_1',B_107) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_107),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_107),'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_176])).

tff(c_217,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_210])).

tff(c_223,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_130,c_217])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_223])).

tff(c_226,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_227,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_229,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_40])).

tff(c_42,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_231,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_42])).

tff(c_44,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_260,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_44])).

tff(c_340,plain,(
    ! [A_132,B_133] :
      ( k1_tops_1(A_132,B_133) = k1_xboole_0
      | ~ v2_tops_1(B_133,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_346,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_340])).

tff(c_353,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_227,c_346])).

tff(c_567,plain,(
    ! [B_161,A_162,C_163] :
      ( r1_tarski(B_161,k1_tops_1(A_162,C_163))
      | ~ r1_tarski(B_161,C_163)
      | ~ v3_pre_topc(B_161,A_162)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_575,plain,(
    ! [B_161] :
      ( r1_tarski(B_161,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_161,'#skF_2')
      | ~ v3_pre_topc(B_161,'#skF_1')
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_567])).

tff(c_586,plain,(
    ! [B_164] :
      ( r1_tarski(B_164,k1_xboole_0)
      | ~ r1_tarski(B_164,'#skF_2')
      | ~ v3_pre_topc(B_164,'#skF_1')
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_353,c_575])).

tff(c_596,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_260,c_586])).

tff(c_608,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_231,c_596])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_613,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_608,c_2])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_616,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_4])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_616])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  
% 2.65/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.36  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.65/1.36  
% 2.65/1.36  %Foreground sorts:
% 2.65/1.36  
% 2.65/1.36  
% 2.65/1.36  %Background operators:
% 2.65/1.36  
% 2.65/1.36  
% 2.65/1.36  %Foreground operators:
% 2.65/1.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.36  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.65/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.65/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.36  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.65/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.65/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.65/1.36  
% 2.65/1.37  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 2.65/1.37  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 2.65/1.37  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.65/1.37  tff(f_59, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.65/1.37  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.65/1.37  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 2.65/1.37  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.65/1.37  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.65/1.37  tff(c_38, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.37  tff(c_64, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 2.65/1.37  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.37  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.37  tff(c_139, plain, (![B_83, A_84]: (v2_tops_1(B_83, A_84) | k1_tops_1(A_84, B_83)!=k1_xboole_0 | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.65/1.37  tff(c_142, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_139])).
% 2.65/1.37  tff(c_145, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_142])).
% 2.65/1.37  tff(c_146, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_64, c_145])).
% 2.65/1.37  tff(c_102, plain, (![A_72, B_73]: (r1_tarski(k1_tops_1(A_72, B_73), B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.65/1.37  tff(c_104, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_102])).
% 2.65/1.37  tff(c_107, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_104])).
% 2.65/1.37  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.37  tff(c_125, plain, (![A_79, B_80]: (v3_pre_topc(k1_tops_1(A_79, B_80), A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.37  tff(c_127, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_125])).
% 2.65/1.37  tff(c_130, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_127])).
% 2.65/1.37  tff(c_20, plain, (![A_33, B_34]: (m1_subset_1(k1_tops_1(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.65/1.37  tff(c_56, plain, (![C_57]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_57 | ~v3_pre_topc(C_57, '#skF_1') | ~r1_tarski(C_57, '#skF_2') | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.37  tff(c_172, plain, (![C_93]: (k1_xboole_0=C_93 | ~v3_pre_topc(C_93, '#skF_1') | ~r1_tarski(C_93, '#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_56])).
% 2.65/1.37  tff(c_176, plain, (![B_34]: (k1_tops_1('#skF_1', B_34)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_34), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_34), '#skF_2') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_172])).
% 2.65/1.37  tff(c_210, plain, (![B_107]: (k1_tops_1('#skF_1', B_107)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_107), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_107), '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_176])).
% 2.65/1.37  tff(c_217, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_32, c_210])).
% 2.65/1.37  tff(c_223, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_107, c_130, c_217])).
% 2.65/1.37  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_223])).
% 2.65/1.37  tff(c_226, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 2.65/1.37  tff(c_227, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 2.65/1.37  tff(c_40, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.37  tff(c_229, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_40])).
% 2.65/1.37  tff(c_42, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.37  tff(c_231, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_42])).
% 2.65/1.37  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.65/1.37  tff(c_260, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_44])).
% 2.65/1.37  tff(c_340, plain, (![A_132, B_133]: (k1_tops_1(A_132, B_133)=k1_xboole_0 | ~v2_tops_1(B_133, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.65/1.37  tff(c_346, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_340])).
% 2.65/1.37  tff(c_353, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_227, c_346])).
% 2.65/1.37  tff(c_567, plain, (![B_161, A_162, C_163]: (r1_tarski(B_161, k1_tops_1(A_162, C_163)) | ~r1_tarski(B_161, C_163) | ~v3_pre_topc(B_161, A_162) | ~m1_subset_1(C_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.65/1.37  tff(c_575, plain, (![B_161]: (r1_tarski(B_161, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_161, '#skF_2') | ~v3_pre_topc(B_161, '#skF_1') | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_567])).
% 2.65/1.37  tff(c_586, plain, (![B_164]: (r1_tarski(B_164, k1_xboole_0) | ~r1_tarski(B_164, '#skF_2') | ~v3_pre_topc(B_164, '#skF_1') | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_353, c_575])).
% 2.65/1.37  tff(c_596, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_260, c_586])).
% 2.65/1.37  tff(c_608, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_229, c_231, c_596])).
% 2.65/1.37  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.37  tff(c_613, plain, (k3_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_608, c_2])).
% 2.65/1.37  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.37  tff(c_616, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_613, c_4])).
% 2.65/1.37  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_616])).
% 2.65/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.37  
% 2.65/1.37  Inference rules
% 2.65/1.37  ----------------------
% 2.65/1.37  #Ref     : 0
% 2.65/1.37  #Sup     : 119
% 2.65/1.37  #Fact    : 0
% 2.65/1.37  #Define  : 0
% 2.65/1.37  #Split   : 6
% 2.65/1.37  #Chain   : 0
% 2.65/1.37  #Close   : 0
% 2.65/1.37  
% 2.65/1.37  Ordering : KBO
% 2.65/1.37  
% 2.65/1.37  Simplification rules
% 2.65/1.37  ----------------------
% 2.65/1.37  #Subsume      : 8
% 2.65/1.37  #Demod        : 150
% 2.65/1.37  #Tautology    : 77
% 2.65/1.37  #SimpNegUnit  : 5
% 2.65/1.37  #BackRed      : 5
% 2.65/1.37  
% 2.65/1.37  #Partial instantiations: 0
% 2.65/1.37  #Strategies tried      : 1
% 2.65/1.37  
% 2.65/1.37  Timing (in seconds)
% 2.65/1.37  ----------------------
% 2.65/1.38  Preprocessing        : 0.32
% 2.65/1.38  Parsing              : 0.17
% 2.65/1.38  CNF conversion       : 0.02
% 2.65/1.38  Main loop            : 0.29
% 2.65/1.38  Inferencing          : 0.11
% 2.65/1.38  Reduction            : 0.09
% 2.65/1.38  Demodulation         : 0.07
% 2.65/1.38  BG Simplification    : 0.02
% 2.65/1.38  Subsumption          : 0.05
% 2.65/1.38  Abstraction          : 0.01
% 2.65/1.38  MUC search           : 0.00
% 2.65/1.38  Cooper               : 0.00
% 2.65/1.38  Total                : 0.65
% 2.65/1.38  Index Insertion      : 0.00
% 2.65/1.38  Index Deletion       : 0.00
% 2.65/1.38  Index Matching       : 0.00
% 2.65/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
