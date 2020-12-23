%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:30 EST 2020

% Result     : Theorem 7.04s
% Output     : CNFRefutation 7.04s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 149 expanded)
%              Number of leaves         :   43 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  138 ( 284 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_106,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_90,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_120,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_62,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    ! [A_40] :
      ( l1_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_97,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_166,plain,(
    ! [A_71] :
      ( u1_struct_0(A_71) = k2_struct_0(A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_50,c_97])).

tff(c_170,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_166])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_171,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_64])).

tff(c_178,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(A_75,B_76)
      | ~ m1_subset_1(A_75,k1_zfmisc_1(B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_187,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_171,c_178])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_74,plain,(
    ! [A_55] :
      ( v1_xboole_0('#skF_3'(A_55))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_24,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_83,plain,(
    ! [A_62] :
      ( '#skF_3'(A_62) = k1_xboole_0
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_74,c_24])).

tff(c_87,plain,(
    '#skF_3'('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_83])).

tff(c_58,plain,(
    ! [A_49] :
      ( v1_xboole_0('#skF_3'(A_49))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_91,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_58])).

tff(c_95,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_91])).

tff(c_246,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_2'(A_86,B_87),B_87)
      | r1_xboole_0(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_267,plain,(
    ! [B_88,A_89] :
      ( ~ v1_xboole_0(B_88)
      | r1_xboole_0(A_89,B_88) ) ),
    inference(resolution,[status(thm)],[c_246,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_299,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(A_90,B_91) = k1_xboole_0
      | ~ v1_xboole_0(B_91) ) ),
    inference(resolution,[status(thm)],[c_267,c_8])).

tff(c_307,plain,(
    ! [A_92] : k3_xboole_0(A_92,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_299])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_315,plain,(
    ! [A_92] : k3_xboole_0(k1_xboole_0,A_92) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_2])).

tff(c_598,plain,(
    ! [B_111,A_112] :
      ( r2_hidden(B_111,A_112)
      | k3_xboole_0(A_112,k1_tarski(B_111)) != k1_tarski(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_630,plain,(
    ! [B_116] :
      ( r2_hidden(B_116,k1_xboole_0)
      | k1_tarski(B_116) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_598])).

tff(c_636,plain,(
    ! [B_116] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_tarski(B_116) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_630,c_4])).

tff(c_640,plain,(
    ! [B_116] : k1_tarski(B_116) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_636])).

tff(c_198,plain,(
    ! [A_81,B_82] :
      ( r1_xboole_0(k1_tarski(A_81),B_82)
      | r2_hidden(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_954,plain,(
    ! [A_132,B_133] :
      ( k3_xboole_0(k1_tarski(A_132),B_133) = k1_xboole_0
      | r2_hidden(A_132,B_133) ) ),
    inference(resolution,[status(thm)],[c_198,c_8])).

tff(c_36,plain,(
    ! [A_28] : r1_tarski(k1_tarski(A_28),k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_203,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_224,plain,(
    ! [A_28] : k3_xboole_0(k1_tarski(A_28),k1_zfmisc_1(A_28)) = k1_tarski(A_28) ),
    inference(resolution,[status(thm)],[c_36,c_203])).

tff(c_984,plain,(
    ! [A_132] :
      ( k1_tarski(A_132) = k1_xboole_0
      | r2_hidden(A_132,k1_zfmisc_1(A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_224])).

tff(c_1047,plain,(
    ! [A_134] : r2_hidden(A_134,k1_zfmisc_1(A_134)) ),
    inference(negUnitSimplification,[status(thm)],[c_640,c_984])).

tff(c_42,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1054,plain,(
    ! [A_134] : m1_subset_1(A_134,k1_zfmisc_1(A_134)) ),
    inference(resolution,[status(thm)],[c_1047,c_42])).

tff(c_52,plain,(
    ! [A_41] :
      ( k1_tops_1(A_41,k2_struct_0(A_41)) = k2_struct_0(A_41)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2231,plain,(
    ! [C_178,A_179,B_180] :
      ( m2_connsp_2(C_178,A_179,B_180)
      | ~ r1_tarski(B_180,k1_tops_1(A_179,C_178))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_7969,plain,(
    ! [A_351,B_352] :
      ( m2_connsp_2(k2_struct_0(A_351),A_351,B_352)
      | ~ r1_tarski(B_352,k2_struct_0(A_351))
      | ~ m1_subset_1(k2_struct_0(A_351),k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2231])).

tff(c_7974,plain,(
    ! [B_352] :
      ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4',B_352)
      | ~ r1_tarski(B_352,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_7969])).

tff(c_8192,plain,(
    ! [B_356] :
      ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4',B_356)
      | ~ r1_tarski(B_356,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_68,c_66,c_170,c_1054,c_7974])).

tff(c_8244,plain,
    ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5')
    | ~ r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_171,c_8192])).

tff(c_8279,plain,(
    m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_8244])).

tff(c_8281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:08:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.04/2.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.04/2.54  
% 7.04/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.04/2.55  %$ m2_connsp_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 7.04/2.55  
% 7.04/2.55  %Foreground sorts:
% 7.04/2.55  
% 7.04/2.55  
% 7.04/2.55  %Background operators:
% 7.04/2.55  
% 7.04/2.55  
% 7.04/2.55  %Foreground operators:
% 7.04/2.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.04/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.04/2.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.04/2.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.04/2.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.04/2.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.04/2.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.04/2.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.04/2.55  tff('#skF_5', type, '#skF_5': $i).
% 7.04/2.55  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.04/2.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.04/2.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.04/2.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.04/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.04/2.55  tff('#skF_4', type, '#skF_4': $i).
% 7.04/2.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.04/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.04/2.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.04/2.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.04/2.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.04/2.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.04/2.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.04/2.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.04/2.55  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 7.04/2.55  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.04/2.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.04/2.55  
% 7.04/2.56  tff(f_154, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 7.04/2.56  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.04/2.56  tff(f_110, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.04/2.56  tff(f_106, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.04/2.56  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_connsp_1)).
% 7.04/2.56  tff(f_73, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 7.04/2.56  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.04/2.56  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.04/2.56  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.04/2.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.04/2.56  tff(f_88, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 7.04/2.56  tff(f_78, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.04/2.56  tff(f_90, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 7.04/2.56  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.04/2.56  tff(f_102, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.04/2.56  tff(f_120, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 7.04/2.56  tff(f_134, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 7.04/2.56  tff(c_62, plain, (~m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.04/2.56  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.04/2.56  tff(c_50, plain, (![A_40]: (l1_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.04/2.56  tff(c_97, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.04/2.56  tff(c_166, plain, (![A_71]: (u1_struct_0(A_71)=k2_struct_0(A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_50, c_97])).
% 7.04/2.56  tff(c_170, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_166])).
% 7.04/2.56  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.04/2.56  tff(c_171, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_64])).
% 7.04/2.56  tff(c_178, plain, (![A_75, B_76]: (r1_tarski(A_75, B_76) | ~m1_subset_1(A_75, k1_zfmisc_1(B_76)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.04/2.56  tff(c_187, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_171, c_178])).
% 7.04/2.56  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.04/2.56  tff(c_74, plain, (![A_55]: (v1_xboole_0('#skF_3'(A_55)) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.04/2.56  tff(c_24, plain, (![A_21]: (k1_xboole_0=A_21 | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.04/2.56  tff(c_83, plain, (![A_62]: ('#skF_3'(A_62)=k1_xboole_0 | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_74, c_24])).
% 7.04/2.56  tff(c_87, plain, ('#skF_3'('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_83])).
% 7.04/2.56  tff(c_58, plain, (![A_49]: (v1_xboole_0('#skF_3'(A_49)) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.04/2.56  tff(c_91, plain, (v1_xboole_0(k1_xboole_0) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_87, c_58])).
% 7.04/2.56  tff(c_95, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_91])).
% 7.04/2.56  tff(c_246, plain, (![A_86, B_87]: (r2_hidden('#skF_2'(A_86, B_87), B_87) | r1_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.04/2.56  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.04/2.56  tff(c_267, plain, (![B_88, A_89]: (~v1_xboole_0(B_88) | r1_xboole_0(A_89, B_88))), inference(resolution, [status(thm)], [c_246, c_4])).
% 7.04/2.56  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.04/2.56  tff(c_299, plain, (![A_90, B_91]: (k3_xboole_0(A_90, B_91)=k1_xboole_0 | ~v1_xboole_0(B_91))), inference(resolution, [status(thm)], [c_267, c_8])).
% 7.04/2.56  tff(c_307, plain, (![A_92]: (k3_xboole_0(A_92, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_95, c_299])).
% 7.04/2.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.04/2.56  tff(c_315, plain, (![A_92]: (k3_xboole_0(k1_xboole_0, A_92)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_307, c_2])).
% 7.04/2.56  tff(c_598, plain, (![B_111, A_112]: (r2_hidden(B_111, A_112) | k3_xboole_0(A_112, k1_tarski(B_111))!=k1_tarski(B_111))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.04/2.56  tff(c_630, plain, (![B_116]: (r2_hidden(B_116, k1_xboole_0) | k1_tarski(B_116)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_315, c_598])).
% 7.04/2.56  tff(c_636, plain, (![B_116]: (~v1_xboole_0(k1_xboole_0) | k1_tarski(B_116)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_630, c_4])).
% 7.04/2.56  tff(c_640, plain, (![B_116]: (k1_tarski(B_116)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_636])).
% 7.04/2.56  tff(c_198, plain, (![A_81, B_82]: (r1_xboole_0(k1_tarski(A_81), B_82) | r2_hidden(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.04/2.56  tff(c_954, plain, (![A_132, B_133]: (k3_xboole_0(k1_tarski(A_132), B_133)=k1_xboole_0 | r2_hidden(A_132, B_133))), inference(resolution, [status(thm)], [c_198, c_8])).
% 7.04/2.56  tff(c_36, plain, (![A_28]: (r1_tarski(k1_tarski(A_28), k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.04/2.56  tff(c_203, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.04/2.56  tff(c_224, plain, (![A_28]: (k3_xboole_0(k1_tarski(A_28), k1_zfmisc_1(A_28))=k1_tarski(A_28))), inference(resolution, [status(thm)], [c_36, c_203])).
% 7.04/2.56  tff(c_984, plain, (![A_132]: (k1_tarski(A_132)=k1_xboole_0 | r2_hidden(A_132, k1_zfmisc_1(A_132)))), inference(superposition, [status(thm), theory('equality')], [c_954, c_224])).
% 7.04/2.56  tff(c_1047, plain, (![A_134]: (r2_hidden(A_134, k1_zfmisc_1(A_134)))), inference(negUnitSimplification, [status(thm)], [c_640, c_984])).
% 7.04/2.56  tff(c_42, plain, (![A_35, B_36]: (m1_subset_1(A_35, B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.04/2.56  tff(c_1054, plain, (![A_134]: (m1_subset_1(A_134, k1_zfmisc_1(A_134)))), inference(resolution, [status(thm)], [c_1047, c_42])).
% 7.04/2.56  tff(c_52, plain, (![A_41]: (k1_tops_1(A_41, k2_struct_0(A_41))=k2_struct_0(A_41) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.04/2.56  tff(c_2231, plain, (![C_178, A_179, B_180]: (m2_connsp_2(C_178, A_179, B_180) | ~r1_tarski(B_180, k1_tops_1(A_179, C_178)) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.04/2.56  tff(c_7969, plain, (![A_351, B_352]: (m2_connsp_2(k2_struct_0(A_351), A_351, B_352) | ~r1_tarski(B_352, k2_struct_0(A_351)) | ~m1_subset_1(k2_struct_0(A_351), k1_zfmisc_1(u1_struct_0(A_351))) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0(A_351))) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2231])).
% 7.04/2.56  tff(c_7974, plain, (![B_352]: (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', B_352) | ~r1_tarski(B_352, k2_struct_0('#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_7969])).
% 7.04/2.56  tff(c_8192, plain, (![B_356]: (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', B_356) | ~r1_tarski(B_356, k2_struct_0('#skF_4')) | ~m1_subset_1(B_356, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_68, c_66, c_170, c_1054, c_7974])).
% 7.04/2.56  tff(c_8244, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5') | ~r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_171, c_8192])).
% 7.04/2.56  tff(c_8279, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_8244])).
% 7.04/2.56  tff(c_8281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_8279])).
% 7.04/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.04/2.56  
% 7.04/2.56  Inference rules
% 7.04/2.56  ----------------------
% 7.04/2.56  #Ref     : 0
% 7.04/2.56  #Sup     : 1899
% 7.04/2.56  #Fact    : 1
% 7.04/2.56  #Define  : 0
% 7.04/2.56  #Split   : 8
% 7.04/2.56  #Chain   : 0
% 7.04/2.56  #Close   : 0
% 7.04/2.56  
% 7.04/2.56  Ordering : KBO
% 7.04/2.56  
% 7.04/2.56  Simplification rules
% 7.04/2.56  ----------------------
% 7.04/2.56  #Subsume      : 302
% 7.04/2.56  #Demod        : 1514
% 7.04/2.56  #Tautology    : 956
% 7.04/2.56  #SimpNegUnit  : 62
% 7.04/2.56  #BackRed      : 61
% 7.04/2.56  
% 7.04/2.56  #Partial instantiations: 0
% 7.04/2.56  #Strategies tried      : 1
% 7.04/2.56  
% 7.04/2.56  Timing (in seconds)
% 7.04/2.56  ----------------------
% 7.04/2.57  Preprocessing        : 0.35
% 7.04/2.57  Parsing              : 0.19
% 7.04/2.57  CNF conversion       : 0.02
% 7.04/2.57  Main loop            : 1.38
% 7.04/2.57  Inferencing          : 0.39
% 7.04/2.57  Reduction            : 0.59
% 7.04/2.57  Demodulation         : 0.46
% 7.04/2.57  BG Simplification    : 0.04
% 7.04/2.57  Subsumption          : 0.25
% 7.04/2.57  Abstraction          : 0.06
% 7.04/2.57  MUC search           : 0.00
% 7.04/2.57  Cooper               : 0.00
% 7.04/2.57  Total                : 1.76
% 7.04/2.57  Index Insertion      : 0.00
% 7.04/2.57  Index Deletion       : 0.00
% 7.04/2.57  Index Matching       : 0.00
% 7.04/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
