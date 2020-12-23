%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:20 EST 2020

% Result     : Theorem 5.57s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 131 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  130 ( 332 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v4_pre_topc(B,A) )
             => ( v5_tops_1(B,A)
              <=> v6_tops_1(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tops_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_144,axiom,(
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

tff(c_76,plain,
    ( v5_tops_1('#skF_3','#skF_2')
    | v6_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_92,plain,(
    v6_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_70,plain,
    ( ~ v6_tops_1('#skF_3','#skF_2')
    | ~ v5_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_128,plain,(
    ~ v5_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_70])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1349,plain,(
    ! [A_141,B_142] :
      ( k2_pre_topc(A_141,B_142) = B_142
      | ~ v4_pre_topc(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1360,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1349])).

tff(c_1373,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_1360])).

tff(c_1966,plain,(
    ! [A_153,B_154] :
      ( k1_tops_1(A_153,k2_pre_topc(A_153,B_154)) = B_154
      | ~ v6_tops_1(B_154,A_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1974,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1966])).

tff(c_1985,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_92,c_1373,c_1974])).

tff(c_2013,plain,(
    ! [B_157,A_158] :
      ( v5_tops_1(B_157,A_158)
      | k2_pre_topc(A_158,k1_tops_1(A_158,B_157)) != B_157
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2015,plain,
    ( v5_tops_1('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1985,c_2013])).

tff(c_2017,plain,(
    v5_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1373,c_2015])).

tff(c_2019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_2017])).

tff(c_2021,plain,(
    ~ v6_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3507,plain,(
    ! [A_238,B_239] :
      ( k2_pre_topc(A_238,B_239) = B_239
      | ~ v4_pre_topc(B_239,A_238)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0(A_238)))
      | ~ l1_pre_topc(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3518,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_3507])).

tff(c_3531,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_3518])).

tff(c_3936,plain,(
    ! [B_248,A_249] :
      ( v6_tops_1(B_248,A_249)
      | k1_tops_1(A_249,k2_pre_topc(A_249,B_248)) != B_248
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3940,plain,
    ( v6_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3531,c_3936])).

tff(c_3945,plain,
    ( v6_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_3940])).

tff(c_3946,plain,(
    k1_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2021,c_3945])).

tff(c_3012,plain,(
    ! [A_223,B_224,C_225] :
      ( k7_subset_1(A_223,B_224,C_225) = k4_xboole_0(B_224,C_225)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(A_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3026,plain,(
    ! [C_225] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_225) = k4_xboole_0('#skF_3',C_225) ),
    inference(resolution,[status(thm)],[c_66,c_3012])).

tff(c_4587,plain,(
    ! [A_260,B_261] :
      ( k7_subset_1(u1_struct_0(A_260),B_261,k2_tops_1(A_260,B_261)) = k1_tops_1(A_260,B_261)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ l1_pre_topc(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_4595,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_4587])).

tff(c_4606,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3026,c_4595])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4637,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4606,c_18])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4644,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4637,c_10])).

tff(c_4650,plain,(
    ~ r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_3946,c_4644])).

tff(c_64,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5349,plain,(
    ! [B_278,A_279,C_280] :
      ( r1_tarski(B_278,k1_tops_1(A_279,C_280))
      | ~ r1_tarski(B_278,C_280)
      | ~ v3_pre_topc(B_278,A_279)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ l1_pre_topc(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5359,plain,(
    ! [B_278] :
      ( r1_tarski(B_278,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_278,'#skF_3')
      | ~ v3_pre_topc(B_278,'#skF_2')
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_5349])).

tff(c_5446,plain,(
    ! [B_281] :
      ( r1_tarski(B_281,k1_tops_1('#skF_2','#skF_3'))
      | ~ r1_tarski(B_281,'#skF_3')
      | ~ v3_pre_topc(B_281,'#skF_2')
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5359])).

tff(c_5460,plain,
    ( r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_5446])).

tff(c_5474,plain,(
    r1_tarski('#skF_3',k1_tops_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14,c_5460])).

tff(c_5476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4650,c_5474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.57/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.57/2.11  
% 5.57/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.57/2.11  %$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.57/2.11  
% 5.57/2.11  %Foreground sorts:
% 5.57/2.11  
% 5.57/2.11  
% 5.57/2.11  %Background operators:
% 5.57/2.11  
% 5.57/2.11  
% 5.57/2.11  %Foreground operators:
% 5.57/2.11  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.57/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.57/2.11  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 5.57/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.57/2.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.57/2.11  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.57/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.57/2.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.57/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.57/2.11  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.57/2.11  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.57/2.11  tff('#skF_2', type, '#skF_2': $i).
% 5.57/2.11  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.57/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.57/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.57/2.11  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.57/2.11  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 5.57/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.57/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.57/2.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.57/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.57/2.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.57/2.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.57/2.11  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.57/2.11  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.57/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.57/2.11  
% 5.81/2.13  tff(f_165, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v4_pre_topc(B, A)) => (v5_tops_1(B, A) <=> v6_tops_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tops_1)).
% 5.81/2.13  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.81/2.13  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tops_1)).
% 5.81/2.13  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 5.81/2.13  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.81/2.13  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.81/2.13  tff(f_46, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.81/2.13  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.81/2.13  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 5.81/2.13  tff(c_76, plain, (v5_tops_1('#skF_3', '#skF_2') | v6_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.81/2.13  tff(c_92, plain, (v6_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_76])).
% 5.81/2.13  tff(c_70, plain, (~v6_tops_1('#skF_3', '#skF_2') | ~v5_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.81/2.13  tff(c_128, plain, (~v5_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_70])).
% 5.81/2.13  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.81/2.13  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.81/2.13  tff(c_62, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.81/2.13  tff(c_1349, plain, (![A_141, B_142]: (k2_pre_topc(A_141, B_142)=B_142 | ~v4_pre_topc(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.81/2.13  tff(c_1360, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1349])).
% 5.81/2.13  tff(c_1373, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_1360])).
% 5.81/2.13  tff(c_1966, plain, (![A_153, B_154]: (k1_tops_1(A_153, k2_pre_topc(A_153, B_154))=B_154 | ~v6_tops_1(B_154, A_153) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.81/2.13  tff(c_1974, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1966])).
% 5.81/2.13  tff(c_1985, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_92, c_1373, c_1974])).
% 5.81/2.13  tff(c_2013, plain, (![B_157, A_158]: (v5_tops_1(B_157, A_158) | k2_pre_topc(A_158, k1_tops_1(A_158, B_157))!=B_157 | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.81/2.13  tff(c_2015, plain, (v5_tops_1('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1985, c_2013])).
% 5.81/2.13  tff(c_2017, plain, (v5_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1373, c_2015])).
% 5.81/2.13  tff(c_2019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_2017])).
% 5.81/2.13  tff(c_2021, plain, (~v6_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_76])).
% 5.81/2.13  tff(c_3507, plain, (![A_238, B_239]: (k2_pre_topc(A_238, B_239)=B_239 | ~v4_pre_topc(B_239, A_238) | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0(A_238))) | ~l1_pre_topc(A_238))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.81/2.13  tff(c_3518, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_3507])).
% 5.81/2.13  tff(c_3531, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_3518])).
% 5.81/2.13  tff(c_3936, plain, (![B_248, A_249]: (v6_tops_1(B_248, A_249) | k1_tops_1(A_249, k2_pre_topc(A_249, B_248))!=B_248 | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.81/2.13  tff(c_3940, plain, (v6_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3531, c_3936])).
% 5.81/2.13  tff(c_3945, plain, (v6_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_3940])).
% 5.81/2.13  tff(c_3946, plain, (k1_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2021, c_3945])).
% 5.81/2.13  tff(c_3012, plain, (![A_223, B_224, C_225]: (k7_subset_1(A_223, B_224, C_225)=k4_xboole_0(B_224, C_225) | ~m1_subset_1(B_224, k1_zfmisc_1(A_223)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.81/2.13  tff(c_3026, plain, (![C_225]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_225)=k4_xboole_0('#skF_3', C_225))), inference(resolution, [status(thm)], [c_66, c_3012])).
% 5.81/2.13  tff(c_4587, plain, (![A_260, B_261]: (k7_subset_1(u1_struct_0(A_260), B_261, k2_tops_1(A_260, B_261))=k1_tops_1(A_260, B_261) | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0(A_260))) | ~l1_pre_topc(A_260))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.81/2.13  tff(c_4595, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_4587])).
% 5.81/2.13  tff(c_4606, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3026, c_4595])).
% 5.81/2.13  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.81/2.13  tff(c_4637, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4606, c_18])).
% 5.81/2.13  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.81/2.13  tff(c_4644, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4637, c_10])).
% 5.81/2.13  tff(c_4650, plain, (~r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_3946, c_4644])).
% 5.81/2.13  tff(c_64, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.81/2.13  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.81/2.13  tff(c_5349, plain, (![B_278, A_279, C_280]: (r1_tarski(B_278, k1_tops_1(A_279, C_280)) | ~r1_tarski(B_278, C_280) | ~v3_pre_topc(B_278, A_279) | ~m1_subset_1(C_280, k1_zfmisc_1(u1_struct_0(A_279))) | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0(A_279))) | ~l1_pre_topc(A_279))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.81/2.13  tff(c_5359, plain, (![B_278]: (r1_tarski(B_278, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_278, '#skF_3') | ~v3_pre_topc(B_278, '#skF_2') | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_5349])).
% 5.81/2.13  tff(c_5446, plain, (![B_281]: (r1_tarski(B_281, k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(B_281, '#skF_3') | ~v3_pre_topc(B_281, '#skF_2') | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5359])).
% 5.81/2.13  tff(c_5460, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_5446])).
% 5.81/2.13  tff(c_5474, plain, (r1_tarski('#skF_3', k1_tops_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_14, c_5460])).
% 5.81/2.13  tff(c_5476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4650, c_5474])).
% 5.81/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.13  
% 5.81/2.13  Inference rules
% 5.81/2.13  ----------------------
% 5.81/2.13  #Ref     : 0
% 5.81/2.13  #Sup     : 1287
% 5.81/2.13  #Fact    : 0
% 5.81/2.13  #Define  : 0
% 5.81/2.13  #Split   : 7
% 5.81/2.13  #Chain   : 0
% 5.81/2.13  #Close   : 0
% 5.81/2.13  
% 5.81/2.13  Ordering : KBO
% 5.81/2.13  
% 5.81/2.13  Simplification rules
% 5.81/2.13  ----------------------
% 5.81/2.13  #Subsume      : 26
% 5.81/2.13  #Demod        : 1397
% 5.81/2.13  #Tautology    : 1002
% 5.81/2.13  #SimpNegUnit  : 5
% 5.81/2.13  #BackRed      : 20
% 5.81/2.13  
% 5.81/2.13  #Partial instantiations: 0
% 5.81/2.13  #Strategies tried      : 1
% 5.81/2.13  
% 5.81/2.13  Timing (in seconds)
% 5.81/2.13  ----------------------
% 5.81/2.13  Preprocessing        : 0.37
% 5.81/2.13  Parsing              : 0.19
% 5.81/2.13  CNF conversion       : 0.03
% 5.81/2.13  Main loop            : 0.98
% 5.81/2.13  Inferencing          : 0.30
% 5.81/2.13  Reduction            : 0.43
% 5.81/2.13  Demodulation         : 0.34
% 5.81/2.13  BG Simplification    : 0.04
% 5.81/2.13  Subsumption          : 0.15
% 5.81/2.13  Abstraction          : 0.06
% 5.81/2.13  MUC search           : 0.00
% 5.81/2.13  Cooper               : 0.00
% 5.81/2.13  Total                : 1.39
% 5.81/2.13  Index Insertion      : 0.00
% 5.81/2.13  Index Deletion       : 0.00
% 5.81/2.13  Index Matching       : 0.00
% 5.81/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
