%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:54 EST 2020

% Result     : Theorem 8.37s
% Output     : CNFRefutation 8.46s
% Verified   : 
% Statistics : Number of formulae       :   79 (  98 expanded)
%              Number of leaves         :   40 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 144 expanded)
%              Number of equality atoms :   31 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_90,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_78,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_68,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_64,plain,(
    ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_66,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3336,plain,(
    ! [A_226,B_227] :
      ( k2_pre_topc(A_226,B_227) = B_227
      | ~ v4_pre_topc(B_227,A_226)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3373,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3336])).

tff(c_3387,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_3373])).

tff(c_5293,plain,(
    ! [A_262,B_263] :
      ( k4_subset_1(u1_struct_0(A_262),B_263,k2_tops_1(A_262,B_263)) = k2_pre_topc(A_262,B_263)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5320,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_5293])).

tff(c_5334,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3387,c_5320])).

tff(c_1624,plain,(
    ! [A_158,B_159] :
      ( k4_xboole_0(A_158,B_159) = k3_subset_1(A_158,B_159)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1659,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1624])).

tff(c_44,plain,(
    ! [A_44,B_45] : k6_subset_1(A_44,B_45) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    ! [A_37,B_38] : m1_subset_1(k6_subset_1(A_37,B_38),k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    ! [A_37,B_38] : m1_subset_1(k4_xboole_0(A_37,B_38),k1_zfmisc_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38])).

tff(c_1709,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1659,c_71])).

tff(c_4980,plain,(
    ! [A_256,B_257] :
      ( k2_tops_1(A_256,k3_subset_1(u1_struct_0(A_256),B_257)) = k2_tops_1(A_256,B_257)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_5007,plain,
    ( k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_4980])).

tff(c_5023,plain,(
    k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5007])).

tff(c_58,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k2_tops_1(A_55,B_56),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5030,plain,
    ( m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5023,c_58])).

tff(c_5034,plain,(
    m1_subset_1(k2_tops_1('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1709,c_5030])).

tff(c_48,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5382,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5034,c_48])).

tff(c_50,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,k1_zfmisc_1(B_49))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3650,plain,(
    ! [A_236,B_237,C_238] :
      ( k4_subset_1(A_236,B_237,C_238) = k2_xboole_0(B_237,C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(A_236))
      | ~ m1_subset_1(B_237,k1_zfmisc_1(A_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18031,plain,(
    ! [B_427,B_428,A_429] :
      ( k4_subset_1(B_427,B_428,A_429) = k2_xboole_0(B_428,A_429)
      | ~ m1_subset_1(B_428,k1_zfmisc_1(B_427))
      | ~ r1_tarski(A_429,B_427) ) ),
    inference(resolution,[status(thm)],[c_50,c_3650])).

tff(c_18285,plain,(
    ! [A_433] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_433) = k2_xboole_0('#skF_3',A_433)
      | ~ r1_tarski(A_433,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_68,c_18031])).

tff(c_18346,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5382,c_18285])).

tff(c_18441,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5334,c_18346])).

tff(c_30,plain,(
    ! [B_30,A_29] : k2_tarski(B_30,A_29) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_189,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_416,plain,(
    ! [A_104,B_105] : k3_tarski(k2_tarski(A_104,B_105)) = k2_xboole_0(B_105,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_189])).

tff(c_32,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_439,plain,(
    ! [B_106,A_107] : k2_xboole_0(B_106,A_107) = k2_xboole_0(A_107,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_32])).

tff(c_28,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_470,plain,(
    ! [A_107,B_106] : r1_tarski(A_107,k2_xboole_0(B_106,A_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_28])).

tff(c_18566,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18441,c_470])).

tff(c_18593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_18566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:29:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.37/3.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.40/3.22  
% 8.40/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.40/3.22  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.40/3.22  
% 8.40/3.22  %Foreground sorts:
% 8.40/3.22  
% 8.40/3.22  
% 8.40/3.22  %Background operators:
% 8.40/3.22  
% 8.40/3.22  
% 8.40/3.22  %Foreground operators:
% 8.40/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.40/3.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.40/3.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.40/3.22  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.40/3.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.40/3.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.40/3.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.40/3.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.40/3.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.40/3.22  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.40/3.22  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.40/3.22  tff('#skF_2', type, '#skF_2': $i).
% 8.40/3.22  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.40/3.22  tff('#skF_3', type, '#skF_3': $i).
% 8.40/3.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.40/3.22  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.40/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.40/3.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.40/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.40/3.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.40/3.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.40/3.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.40/3.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.40/3.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.40/3.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.40/3.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.40/3.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.40/3.22  
% 8.46/3.24  tff(f_146, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 8.46/3.24  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.46/3.24  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 8.46/3.24  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 8.46/3.24  tff(f_90, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.46/3.24  tff(f_78, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 8.46/3.24  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 8.46/3.24  tff(f_122, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.46/3.24  tff(f_96, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.46/3.24  tff(f_88, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.46/3.24  tff(f_66, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.46/3.24  tff(f_68, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.46/3.24  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.46/3.24  tff(c_64, plain, (~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.46/3.24  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.46/3.24  tff(c_66, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.46/3.24  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 8.46/3.24  tff(c_3336, plain, (![A_226, B_227]: (k2_pre_topc(A_226, B_227)=B_227 | ~v4_pre_topc(B_227, A_226) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.46/3.24  tff(c_3373, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_3336])).
% 8.46/3.24  tff(c_3387, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_3373])).
% 8.46/3.24  tff(c_5293, plain, (![A_262, B_263]: (k4_subset_1(u1_struct_0(A_262), B_263, k2_tops_1(A_262, B_263))=k2_pre_topc(A_262, B_263) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.46/3.24  tff(c_5320, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_5293])).
% 8.46/3.24  tff(c_5334, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3387, c_5320])).
% 8.46/3.24  tff(c_1624, plain, (![A_158, B_159]: (k4_xboole_0(A_158, B_159)=k3_subset_1(A_158, B_159) | ~m1_subset_1(B_159, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.46/3.24  tff(c_1659, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_68, c_1624])).
% 8.46/3.24  tff(c_44, plain, (![A_44, B_45]: (k6_subset_1(A_44, B_45)=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.46/3.24  tff(c_38, plain, (![A_37, B_38]: (m1_subset_1(k6_subset_1(A_37, B_38), k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.46/3.24  tff(c_71, plain, (![A_37, B_38]: (m1_subset_1(k4_xboole_0(A_37, B_38), k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38])).
% 8.46/3.24  tff(c_1709, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1659, c_71])).
% 8.46/3.24  tff(c_4980, plain, (![A_256, B_257]: (k2_tops_1(A_256, k3_subset_1(u1_struct_0(A_256), B_257))=k2_tops_1(A_256, B_257) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.46/3.24  tff(c_5007, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_4980])).
% 8.46/3.24  tff(c_5023, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5007])).
% 8.46/3.24  tff(c_58, plain, (![A_55, B_56]: (m1_subset_1(k2_tops_1(A_55, B_56), k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.46/3.24  tff(c_5030, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5023, c_58])).
% 8.46/3.24  tff(c_5034, plain, (m1_subset_1(k2_tops_1('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1709, c_5030])).
% 8.46/3.24  tff(c_48, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.46/3.24  tff(c_5382, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_5034, c_48])).
% 8.46/3.24  tff(c_50, plain, (![A_48, B_49]: (m1_subset_1(A_48, k1_zfmisc_1(B_49)) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.46/3.24  tff(c_3650, plain, (![A_236, B_237, C_238]: (k4_subset_1(A_236, B_237, C_238)=k2_xboole_0(B_237, C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(A_236)) | ~m1_subset_1(B_237, k1_zfmisc_1(A_236)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.46/3.24  tff(c_18031, plain, (![B_427, B_428, A_429]: (k4_subset_1(B_427, B_428, A_429)=k2_xboole_0(B_428, A_429) | ~m1_subset_1(B_428, k1_zfmisc_1(B_427)) | ~r1_tarski(A_429, B_427))), inference(resolution, [status(thm)], [c_50, c_3650])).
% 8.46/3.24  tff(c_18285, plain, (![A_433]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_433)=k2_xboole_0('#skF_3', A_433) | ~r1_tarski(A_433, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_68, c_18031])).
% 8.46/3.24  tff(c_18346, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5382, c_18285])).
% 8.46/3.24  tff(c_18441, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5334, c_18346])).
% 8.46/3.24  tff(c_30, plain, (![B_30, A_29]: (k2_tarski(B_30, A_29)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.46/3.24  tff(c_189, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.46/3.24  tff(c_416, plain, (![A_104, B_105]: (k3_tarski(k2_tarski(A_104, B_105))=k2_xboole_0(B_105, A_104))), inference(superposition, [status(thm), theory('equality')], [c_30, c_189])).
% 8.46/3.24  tff(c_32, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.46/3.24  tff(c_439, plain, (![B_106, A_107]: (k2_xboole_0(B_106, A_107)=k2_xboole_0(A_107, B_106))), inference(superposition, [status(thm), theory('equality')], [c_416, c_32])).
% 8.46/3.24  tff(c_28, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.46/3.24  tff(c_470, plain, (![A_107, B_106]: (r1_tarski(A_107, k2_xboole_0(B_106, A_107)))), inference(superposition, [status(thm), theory('equality')], [c_439, c_28])).
% 8.46/3.24  tff(c_18566, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18441, c_470])).
% 8.46/3.24  tff(c_18593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_18566])).
% 8.46/3.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.46/3.24  
% 8.46/3.24  Inference rules
% 8.46/3.24  ----------------------
% 8.46/3.24  #Ref     : 0
% 8.46/3.24  #Sup     : 4445
% 8.46/3.24  #Fact    : 0
% 8.46/3.24  #Define  : 0
% 8.46/3.24  #Split   : 0
% 8.46/3.24  #Chain   : 0
% 8.46/3.24  #Close   : 0
% 8.46/3.24  
% 8.46/3.24  Ordering : KBO
% 8.46/3.24  
% 8.46/3.24  Simplification rules
% 8.46/3.24  ----------------------
% 8.46/3.24  #Subsume      : 125
% 8.46/3.24  #Demod        : 3744
% 8.46/3.24  #Tautology    : 2995
% 8.46/3.24  #SimpNegUnit  : 1
% 8.46/3.24  #BackRed      : 1
% 8.46/3.24  
% 8.46/3.24  #Partial instantiations: 0
% 8.46/3.24  #Strategies tried      : 1
% 8.46/3.24  
% 8.46/3.24  Timing (in seconds)
% 8.46/3.24  ----------------------
% 8.46/3.24  Preprocessing        : 0.33
% 8.46/3.24  Parsing              : 0.18
% 8.46/3.24  CNF conversion       : 0.02
% 8.46/3.24  Main loop            : 2.16
% 8.46/3.24  Inferencing          : 0.48
% 8.46/3.24  Reduction            : 1.09
% 8.46/3.24  Demodulation         : 0.93
% 8.46/3.24  BG Simplification    : 0.06
% 8.46/3.24  Subsumption          : 0.41
% 8.46/3.24  Abstraction          : 0.08
% 8.46/3.24  MUC search           : 0.00
% 8.46/3.24  Cooper               : 0.00
% 8.46/3.24  Total                : 2.52
% 8.46/3.24  Index Insertion      : 0.00
% 8.46/3.24  Index Deletion       : 0.00
% 8.46/3.24  Index Matching       : 0.00
% 8.46/3.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
