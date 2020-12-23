%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:13 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 121 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 242 expanded)
%              Number of equality atoms :   48 (  77 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_78,axiom,(
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

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7897,plain,(
    ! [A_243,B_244,C_245] :
      ( k7_subset_1(A_243,B_244,C_245) = k4_xboole_0(B_244,C_245)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(A_243)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7900,plain,(
    ! [C_245] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_245) = k4_xboole_0('#skF_2',C_245) ),
    inference(resolution,[status(thm)],[c_38,c_7897])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_112,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1608,plain,(
    ! [B_118,A_119] :
      ( v4_pre_topc(B_118,A_119)
      | k2_pre_topc(A_119,B_118) != B_118
      | ~ v2_pre_topc(A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1614,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1608])).

tff(c_1618,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_1614])).

tff(c_1619,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1618])).

tff(c_1700,plain,(
    ! [A_122,B_123] :
      ( k4_subset_1(u1_struct_0(A_122),B_123,k2_tops_1(A_122,B_123)) = k2_pre_topc(A_122,B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1704,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1700])).

tff(c_1708,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1704])).

tff(c_543,plain,(
    ! [A_75,B_76,C_77] :
      ( k7_subset_1(A_75,B_76,C_77) = k4_xboole_0(B_76,C_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_623,plain,(
    ! [C_81] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_81) = k4_xboole_0('#skF_2',C_81) ),
    inference(resolution,[status(thm)],[c_38,c_543])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_239,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_50])).

tff(c_629,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_239])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_113,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_123,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_20,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_244,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(B_57,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_97])).

tff(c_22,plain,(
    ! [A_17,B_18] : k3_tarski(k2_tarski(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_267,plain,(
    ! [B_58,A_59] : k2_xboole_0(B_58,A_59) = k2_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_22])).

tff(c_321,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_267])).

tff(c_1058,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_321])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_tops_1(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1353,plain,(
    ! [A_105,B_106,C_107] :
      ( k4_subset_1(A_105,B_106,C_107) = k2_xboole_0(B_106,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7366,plain,(
    ! [A_207,B_208,B_209] :
      ( k4_subset_1(u1_struct_0(A_207),B_208,k2_tops_1(A_207,B_209)) = k2_xboole_0(B_208,k2_tops_1(A_207,B_209))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(resolution,[status(thm)],[c_32,c_1353])).

tff(c_7370,plain,(
    ! [B_209] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_209)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_209))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_7366])).

tff(c_7378,plain,(
    ! [B_210] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_210)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_210))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7370])).

tff(c_7385,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_7378])).

tff(c_7390,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1708,c_1058,c_7385])).

tff(c_7392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1619,c_7390])).

tff(c_7393,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8242,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7900,c_7393])).

tff(c_7394,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8165,plain,(
    ! [A_253,B_254] :
      ( k2_pre_topc(A_253,B_254) = B_254
      | ~ v4_pre_topc(B_254,A_253)
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ l1_pre_topc(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8168,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_8165])).

tff(c_8171,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7394,c_8168])).

tff(c_10515,plain,(
    ! [A_315,B_316] :
      ( k7_subset_1(u1_struct_0(A_315),k2_pre_topc(A_315,B_316),k1_tops_1(A_315,B_316)) = k2_tops_1(A_315,B_316)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10524,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8171,c_10515])).

tff(c_10528,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_7900,c_10524])).

tff(c_10530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8242,c_10528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:19:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.20  
% 5.89/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.20  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.89/2.20  
% 5.89/2.20  %Foreground sorts:
% 5.89/2.20  
% 5.89/2.20  
% 5.89/2.20  %Background operators:
% 5.89/2.20  
% 5.89/2.20  
% 5.89/2.20  %Foreground operators:
% 5.89/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.89/2.20  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.89/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.89/2.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.89/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.89/2.20  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.89/2.20  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.89/2.20  tff('#skF_2', type, '#skF_2': $i).
% 5.89/2.20  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.89/2.20  tff('#skF_1', type, '#skF_1': $i).
% 5.89/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.89/2.20  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.89/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.89/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.89/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.89/2.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.89/2.20  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.89/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.89/2.20  
% 5.89/2.22  tff(f_110, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.89/2.22  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.89/2.22  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.89/2.22  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.89/2.22  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.89/2.22  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.89/2.22  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.89/2.22  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.89/2.22  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.89/2.22  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.89/2.22  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.89/2.22  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.89/2.22  tff(c_7897, plain, (![A_243, B_244, C_245]: (k7_subset_1(A_243, B_244, C_245)=k4_xboole_0(B_244, C_245) | ~m1_subset_1(B_244, k1_zfmisc_1(A_243)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.89/2.22  tff(c_7900, plain, (![C_245]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_245)=k4_xboole_0('#skF_2', C_245))), inference(resolution, [status(thm)], [c_38, c_7897])).
% 5.89/2.22  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.89/2.22  tff(c_112, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 5.89/2.22  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.89/2.22  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.89/2.22  tff(c_1608, plain, (![B_118, A_119]: (v4_pre_topc(B_118, A_119) | k2_pre_topc(A_119, B_118)!=B_118 | ~v2_pre_topc(A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.89/2.22  tff(c_1614, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1608])).
% 5.89/2.22  tff(c_1618, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_1614])).
% 5.89/2.22  tff(c_1619, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_112, c_1618])).
% 5.89/2.22  tff(c_1700, plain, (![A_122, B_123]: (k4_subset_1(u1_struct_0(A_122), B_123, k2_tops_1(A_122, B_123))=k2_pre_topc(A_122, B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.89/2.22  tff(c_1704, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1700])).
% 5.89/2.22  tff(c_1708, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1704])).
% 5.89/2.22  tff(c_543, plain, (![A_75, B_76, C_77]: (k7_subset_1(A_75, B_76, C_77)=k4_xboole_0(B_76, C_77) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.89/2.22  tff(c_623, plain, (![C_81]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_81)=k4_xboole_0('#skF_2', C_81))), inference(resolution, [status(thm)], [c_38, c_543])).
% 5.89/2.22  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.89/2.22  tff(c_239, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_112, c_50])).
% 5.89/2.22  tff(c_629, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_623, c_239])).
% 5.89/2.22  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.89/2.22  tff(c_113, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.89/2.22  tff(c_123, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), A_7)=A_7)), inference(resolution, [status(thm)], [c_14, c_113])).
% 5.89/2.22  tff(c_20, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.89/2.22  tff(c_97, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.89/2.22  tff(c_244, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(B_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_20, c_97])).
% 5.89/2.22  tff(c_22, plain, (![A_17, B_18]: (k3_tarski(k2_tarski(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.89/2.22  tff(c_267, plain, (![B_58, A_59]: (k2_xboole_0(B_58, A_59)=k2_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_244, c_22])).
% 5.89/2.22  tff(c_321, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=A_7)), inference(superposition, [status(thm), theory('equality')], [c_123, c_267])).
% 5.89/2.22  tff(c_1058, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_629, c_321])).
% 5.89/2.22  tff(c_32, plain, (![A_28, B_29]: (m1_subset_1(k2_tops_1(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.89/2.22  tff(c_1353, plain, (![A_105, B_106, C_107]: (k4_subset_1(A_105, B_106, C_107)=k2_xboole_0(B_106, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(A_105)) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.89/2.22  tff(c_7366, plain, (![A_207, B_208, B_209]: (k4_subset_1(u1_struct_0(A_207), B_208, k2_tops_1(A_207, B_209))=k2_xboole_0(B_208, k2_tops_1(A_207, B_209)) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(resolution, [status(thm)], [c_32, c_1353])).
% 5.89/2.22  tff(c_7370, plain, (![B_209]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_209))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_209)) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_7366])).
% 5.89/2.22  tff(c_7378, plain, (![B_210]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_210))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_210)) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7370])).
% 5.89/2.22  tff(c_7385, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_7378])).
% 5.89/2.22  tff(c_7390, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1708, c_1058, c_7385])).
% 5.89/2.22  tff(c_7392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1619, c_7390])).
% 5.89/2.22  tff(c_7393, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 5.89/2.22  tff(c_8242, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7900, c_7393])).
% 5.89/2.22  tff(c_7394, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.89/2.22  tff(c_8165, plain, (![A_253, B_254]: (k2_pre_topc(A_253, B_254)=B_254 | ~v4_pre_topc(B_254, A_253) | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0(A_253))) | ~l1_pre_topc(A_253))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.89/2.22  tff(c_8168, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_8165])).
% 5.89/2.22  tff(c_8171, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7394, c_8168])).
% 5.89/2.22  tff(c_10515, plain, (![A_315, B_316]: (k7_subset_1(u1_struct_0(A_315), k2_pre_topc(A_315, B_316), k1_tops_1(A_315, B_316))=k2_tops_1(A_315, B_316) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_315))) | ~l1_pre_topc(A_315))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.89/2.22  tff(c_10524, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8171, c_10515])).
% 5.89/2.22  tff(c_10528, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_7900, c_10524])).
% 5.89/2.22  tff(c_10530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8242, c_10528])).
% 5.89/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.22  
% 5.89/2.22  Inference rules
% 5.89/2.22  ----------------------
% 5.89/2.22  #Ref     : 0
% 5.89/2.22  #Sup     : 2546
% 5.89/2.22  #Fact    : 0
% 5.89/2.22  #Define  : 0
% 5.89/2.22  #Split   : 2
% 5.89/2.22  #Chain   : 0
% 5.89/2.22  #Close   : 0
% 5.89/2.22  
% 5.89/2.22  Ordering : KBO
% 5.89/2.22  
% 5.89/2.22  Simplification rules
% 5.89/2.22  ----------------------
% 5.89/2.22  #Subsume      : 63
% 5.89/2.22  #Demod        : 2527
% 5.89/2.22  #Tautology    : 2061
% 5.89/2.22  #SimpNegUnit  : 4
% 5.89/2.22  #BackRed      : 3
% 5.89/2.22  
% 5.89/2.22  #Partial instantiations: 0
% 5.89/2.22  #Strategies tried      : 1
% 5.89/2.22  
% 5.89/2.22  Timing (in seconds)
% 5.89/2.22  ----------------------
% 5.89/2.22  Preprocessing        : 0.34
% 5.89/2.22  Parsing              : 0.19
% 5.89/2.22  CNF conversion       : 0.02
% 5.89/2.22  Main loop            : 1.13
% 5.89/2.22  Inferencing          : 0.33
% 5.89/2.22  Reduction            : 0.52
% 5.89/2.22  Demodulation         : 0.44
% 5.89/2.22  BG Simplification    : 0.03
% 5.89/2.22  Subsumption          : 0.17
% 5.89/2.22  Abstraction          : 0.06
% 5.89/2.22  MUC search           : 0.00
% 5.89/2.22  Cooper               : 0.00
% 5.89/2.22  Total                : 1.50
% 5.89/2.22  Index Insertion      : 0.00
% 5.89/2.22  Index Deletion       : 0.00
% 5.89/2.22  Index Matching       : 0.00
% 5.89/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
