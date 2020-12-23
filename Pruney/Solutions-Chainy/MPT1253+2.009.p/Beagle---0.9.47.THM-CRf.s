%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:53 EST 2020

% Result     : Theorem 13.07s
% Output     : CNFRefutation 13.07s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 129 expanded)
%              Number of leaves         :   32 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 253 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_58,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_3120,plain,(
    ! [A_214,C_215,B_216] :
      ( r1_tarski(k2_pre_topc(A_214,C_215),B_216)
      | ~ r1_tarski(C_215,B_216)
      | ~ v4_pre_topc(B_216,A_214)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3141,plain,(
    ! [B_216] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_216)
      | ~ r1_tarski('#skF_2',B_216)
      | ~ v4_pre_topc(B_216,'#skF_1')
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_3120])).

tff(c_3383,plain,(
    ! [B_222] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),B_222)
      | ~ r1_tarski('#skF_2',B_222)
      | ~ v4_pre_topc(B_222,'#skF_1')
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3141])).

tff(c_3413,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_3383])).

tff(c_3429,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6,c_3413])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3440,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3429,c_2])).

tff(c_3758,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3440])).

tff(c_1865,plain,(
    ! [A_176,B_177] :
      ( k4_subset_1(u1_struct_0(A_176),B_177,k2_tops_1(A_176,B_177)) = k2_pre_topc(A_176,B_177)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1886,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_1865])).

tff(c_1898,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1886])).

tff(c_50,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k2_tops_1(A_49,B_50),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1359,plain,(
    ! [A_157,B_158,C_159] :
      ( k4_subset_1(A_157,B_158,C_159) = k2_xboole_0(B_158,C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(A_157))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14761,plain,(
    ! [A_404,B_405,B_406] :
      ( k4_subset_1(u1_struct_0(A_404),B_405,k2_tops_1(A_404,B_406)) = k2_xboole_0(B_405,k2_tops_1(A_404,B_406))
      | ~ m1_subset_1(B_405,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ l1_pre_topc(A_404) ) ),
    inference(resolution,[status(thm)],[c_50,c_1359])).

tff(c_14782,plain,(
    ! [B_406] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_406)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_406))
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_14761])).

tff(c_24458,plain,(
    ! [B_505] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_505)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_505))
      | ~ m1_subset_1(B_505,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14782])).

tff(c_24491,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_24458])).

tff(c_24505,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1898,c_24491])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24636,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24505,c_26])).

tff(c_24644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3758,c_24636])).

tff(c_24645,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3440])).

tff(c_24651,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24645,c_1898])).

tff(c_35078,plain,(
    ! [A_679,B_680,B_681] :
      ( k4_subset_1(u1_struct_0(A_679),B_680,k2_tops_1(A_679,B_681)) = k2_xboole_0(B_680,k2_tops_1(A_679,B_681))
      | ~ m1_subset_1(B_680,k1_zfmisc_1(u1_struct_0(A_679)))
      | ~ m1_subset_1(B_681,k1_zfmisc_1(u1_struct_0(A_679)))
      | ~ l1_pre_topc(A_679) ) ),
    inference(resolution,[status(thm)],[c_50,c_1359])).

tff(c_35099,plain,(
    ! [B_681] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_681)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_681))
      | ~ m1_subset_1(B_681,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_35078])).

tff(c_43792,plain,(
    ! [B_772] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_772)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_772))
      | ~ m1_subset_1(B_772,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_35099])).

tff(c_43825,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_43792])).

tff(c_43839,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24651,c_43825])).

tff(c_28,plain,(
    ! [B_24,A_23] : k2_tarski(B_24,A_23) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_174,plain,(
    ! [A_82,B_83] : k3_tarski(k2_tarski(A_82,B_83)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_291,plain,(
    ! [B_91,A_92] : k3_tarski(k2_tarski(B_91,A_92)) = k2_xboole_0(A_92,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_174])).

tff(c_30,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_314,plain,(
    ! [B_93,A_94] : k2_xboole_0(B_93,A_94) = k2_xboole_0(A_94,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_30])).

tff(c_329,plain,(
    ! [A_94,B_93] : r1_tarski(A_94,k2_xboole_0(B_93,A_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_26])).

tff(c_43966,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_43839,c_329])).

tff(c_43995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_43966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:50:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.07/6.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.07/6.24  
% 13.07/6.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.07/6.24  %$ v4_pre_topc > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 13.07/6.24  
% 13.07/6.24  %Foreground sorts:
% 13.07/6.24  
% 13.07/6.24  
% 13.07/6.24  %Background operators:
% 13.07/6.24  
% 13.07/6.24  
% 13.07/6.24  %Foreground operators:
% 13.07/6.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.07/6.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.07/6.24  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 13.07/6.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.07/6.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.07/6.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.07/6.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.07/6.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.07/6.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 13.07/6.24  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 13.07/6.24  tff('#skF_2', type, '#skF_2': $i).
% 13.07/6.24  tff('#skF_1', type, '#skF_1': $i).
% 13.07/6.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.07/6.24  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 13.07/6.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.07/6.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.07/6.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.07/6.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.07/6.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.07/6.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.07/6.24  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 13.07/6.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.07/6.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.07/6.24  
% 13.07/6.25  tff(f_149, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 13.07/6.25  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.07/6.25  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 13.07/6.25  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 13.07/6.25  tff(f_111, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 13.07/6.25  tff(f_83, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 13.07/6.25  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.07/6.25  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.07/6.25  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.07/6.25  tff(c_58, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.07/6.25  tff(c_60, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.07/6.25  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.07/6.25  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.07/6.25  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 13.07/6.25  tff(c_3120, plain, (![A_214, C_215, B_216]: (r1_tarski(k2_pre_topc(A_214, C_215), B_216) | ~r1_tarski(C_215, B_216) | ~v4_pre_topc(B_216, A_214) | ~m1_subset_1(C_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_125])).
% 13.07/6.25  tff(c_3141, plain, (![B_216]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_216) | ~r1_tarski('#skF_2', B_216) | ~v4_pre_topc(B_216, '#skF_1') | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_3120])).
% 13.07/6.25  tff(c_3383, plain, (![B_222]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), B_222) | ~r1_tarski('#skF_2', B_222) | ~v4_pre_topc(B_222, '#skF_1') | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3141])).
% 13.07/6.25  tff(c_3413, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_3383])).
% 13.07/6.25  tff(c_3429, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6, c_3413])).
% 13.07/6.25  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.07/6.25  tff(c_3440, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_3429, c_2])).
% 13.07/6.25  tff(c_3758, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3440])).
% 13.07/6.25  tff(c_1865, plain, (![A_176, B_177]: (k4_subset_1(u1_struct_0(A_176), B_177, k2_tops_1(A_176, B_177))=k2_pre_topc(A_176, B_177) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.07/6.25  tff(c_1886, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_1865])).
% 13.07/6.25  tff(c_1898, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1886])).
% 13.07/6.25  tff(c_50, plain, (![A_49, B_50]: (m1_subset_1(k2_tops_1(A_49, B_50), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.07/6.25  tff(c_1359, plain, (![A_157, B_158, C_159]: (k4_subset_1(A_157, B_158, C_159)=k2_xboole_0(B_158, C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)) | ~m1_subset_1(B_158, k1_zfmisc_1(A_157)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.07/6.25  tff(c_14761, plain, (![A_404, B_405, B_406]: (k4_subset_1(u1_struct_0(A_404), B_405, k2_tops_1(A_404, B_406))=k2_xboole_0(B_405, k2_tops_1(A_404, B_406)) | ~m1_subset_1(B_405, k1_zfmisc_1(u1_struct_0(A_404))) | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0(A_404))) | ~l1_pre_topc(A_404))), inference(resolution, [status(thm)], [c_50, c_1359])).
% 13.07/6.25  tff(c_14782, plain, (![B_406]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_406))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_406)) | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_14761])).
% 13.07/6.25  tff(c_24458, plain, (![B_505]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_505))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_505)) | ~m1_subset_1(B_505, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_14782])).
% 13.07/6.25  tff(c_24491, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_24458])).
% 13.07/6.25  tff(c_24505, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1898, c_24491])).
% 13.07/6.25  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.07/6.25  tff(c_24636, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24505, c_26])).
% 13.07/6.25  tff(c_24644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3758, c_24636])).
% 13.07/6.25  tff(c_24645, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_3440])).
% 13.07/6.25  tff(c_24651, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24645, c_1898])).
% 13.07/6.25  tff(c_35078, plain, (![A_679, B_680, B_681]: (k4_subset_1(u1_struct_0(A_679), B_680, k2_tops_1(A_679, B_681))=k2_xboole_0(B_680, k2_tops_1(A_679, B_681)) | ~m1_subset_1(B_680, k1_zfmisc_1(u1_struct_0(A_679))) | ~m1_subset_1(B_681, k1_zfmisc_1(u1_struct_0(A_679))) | ~l1_pre_topc(A_679))), inference(resolution, [status(thm)], [c_50, c_1359])).
% 13.07/6.25  tff(c_35099, plain, (![B_681]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_681))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_681)) | ~m1_subset_1(B_681, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_35078])).
% 13.07/6.25  tff(c_43792, plain, (![B_772]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_772))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_772)) | ~m1_subset_1(B_772, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_35099])).
% 13.07/6.25  tff(c_43825, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_43792])).
% 13.07/6.25  tff(c_43839, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24651, c_43825])).
% 13.07/6.25  tff(c_28, plain, (![B_24, A_23]: (k2_tarski(B_24, A_23)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.07/6.25  tff(c_174, plain, (![A_82, B_83]: (k3_tarski(k2_tarski(A_82, B_83))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.07/6.25  tff(c_291, plain, (![B_91, A_92]: (k3_tarski(k2_tarski(B_91, A_92))=k2_xboole_0(A_92, B_91))), inference(superposition, [status(thm), theory('equality')], [c_28, c_174])).
% 13.07/6.25  tff(c_30, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.07/6.25  tff(c_314, plain, (![B_93, A_94]: (k2_xboole_0(B_93, A_94)=k2_xboole_0(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_291, c_30])).
% 13.07/6.25  tff(c_329, plain, (![A_94, B_93]: (r1_tarski(A_94, k2_xboole_0(B_93, A_94)))), inference(superposition, [status(thm), theory('equality')], [c_314, c_26])).
% 13.07/6.25  tff(c_43966, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_43839, c_329])).
% 13.07/6.25  tff(c_43995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_43966])).
% 13.07/6.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.07/6.25  
% 13.07/6.25  Inference rules
% 13.07/6.25  ----------------------
% 13.07/6.25  #Ref     : 0
% 13.07/6.25  #Sup     : 10596
% 13.07/6.25  #Fact    : 0
% 13.07/6.25  #Define  : 0
% 13.07/6.25  #Split   : 6
% 13.07/6.25  #Chain   : 0
% 13.07/6.25  #Close   : 0
% 13.07/6.25  
% 13.07/6.25  Ordering : KBO
% 13.07/6.25  
% 13.07/6.25  Simplification rules
% 13.07/6.25  ----------------------
% 13.07/6.25  #Subsume      : 375
% 13.07/6.25  #Demod        : 11723
% 13.07/6.25  #Tautology    : 7426
% 13.07/6.25  #SimpNegUnit  : 3
% 13.07/6.25  #BackRed      : 13
% 13.07/6.25  
% 13.07/6.25  #Partial instantiations: 0
% 13.07/6.25  #Strategies tried      : 1
% 13.07/6.25  
% 13.07/6.25  Timing (in seconds)
% 13.07/6.25  ----------------------
% 13.07/6.25  Preprocessing        : 0.35
% 13.07/6.25  Parsing              : 0.20
% 13.07/6.25  CNF conversion       : 0.02
% 13.07/6.25  Main loop            : 5.09
% 13.07/6.25  Inferencing          : 0.92
% 13.07/6.25  Reduction            : 2.87
% 13.07/6.25  Demodulation         : 2.50
% 13.07/6.25  BG Simplification    : 0.10
% 13.07/6.25  Subsumption          : 0.95
% 13.07/6.25  Abstraction          : 0.17
% 13.07/6.25  MUC search           : 0.00
% 13.07/6.25  Cooper               : 0.00
% 13.07/6.25  Total                : 5.47
% 13.07/6.25  Index Insertion      : 0.00
% 13.07/6.25  Index Deletion       : 0.00
% 13.07/6.25  Index Matching       : 0.00
% 13.07/6.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
