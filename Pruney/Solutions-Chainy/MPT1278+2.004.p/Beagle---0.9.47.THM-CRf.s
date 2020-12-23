%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:09 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 166 expanded)
%              Number of leaves         :   37 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  151 ( 457 expanded)
%              Number of equality atoms :   23 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_90,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_104,axiom,(
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

tff(f_38,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,B))) = k2_pre_topc(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_46,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_286,plain,(
    ! [B_95,A_96] :
      ( v4_pre_topc(B_95,A_96)
      | ~ v1_xboole_0(B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_308,plain,(
    ! [A_96] :
      ( v4_pre_topc(k1_xboole_0,A_96)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_20,c_286])).

tff(c_320,plain,(
    ! [A_96] :
      ( v4_pre_topc(k1_xboole_0,A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_308])).

tff(c_1387,plain,(
    ! [A_217,B_218] :
      ( k2_pre_topc(A_217,B_218) = B_218
      | ~ v4_pre_topc(B_218,A_217)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1436,plain,(
    ! [A_219] :
      ( k2_pre_topc(A_219,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_219)
      | ~ l1_pre_topc(A_219) ) ),
    inference(resolution,[status(thm)],[c_20,c_1387])).

tff(c_1486,plain,(
    ! [A_222] :
      ( k2_pre_topc(A_222,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222) ) ),
    inference(resolution,[status(thm)],[c_320,c_1436])).

tff(c_1489,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1486])).

tff(c_1492,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1489])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_304,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v1_xboole_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_286])).

tff(c_317,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_304])).

tff(c_321,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_174,plain,(
    ! [B_74,A_75] :
      ( v2_tops_1(B_74,A_75)
      | ~ v3_tops_1(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_188,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_174])).

tff(c_200,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_188])).

tff(c_546,plain,(
    ! [A_130,B_131] :
      ( k1_tops_1(A_130,B_131) = k1_xboole_0
      | ~ v2_tops_1(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_570,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_546])).

tff(c_589,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_200,c_570])).

tff(c_976,plain,(
    ! [B_172,A_173,C_174] :
      ( r1_tarski(B_172,k1_tops_1(A_173,C_174))
      | ~ r1_tarski(B_172,C_174)
      | ~ v3_pre_topc(B_172,A_173)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_996,plain,(
    ! [B_172] :
      ( r1_tarski(B_172,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_172,'#skF_2')
      | ~ v3_pre_topc(B_172,'#skF_1')
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_976])).

tff(c_1017,plain,(
    ! [B_175] :
      ( r1_tarski(B_175,k1_xboole_0)
      | ~ r1_tarski(B_175,'#skF_2')
      | ~ v3_pre_topc(B_175,'#skF_1')
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_589,c_996])).

tff(c_1045,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1017])).

tff(c_1059,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_1045])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,(
    ! [B_53,A_54] :
      ( ~ r1_xboole_0(B_53,A_54)
      | ~ r1_tarski(B_53,A_54)
      | v1_xboole_0(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_91,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_87])).

tff(c_1064,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1059,c_91])).

tff(c_1073,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_1064])).

tff(c_1074,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_1411,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1387])).

tff(c_1430,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1074,c_1411])).

tff(c_1301,plain,(
    ! [A_209,B_210] :
      ( k1_tops_1(A_209,B_210) = k1_xboole_0
      | ~ v2_tops_1(B_210,A_209)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1325,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1301])).

tff(c_1344,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_200,c_1325])).

tff(c_1627,plain,(
    ! [A_241,B_242] :
      ( k2_pre_topc(A_241,k1_tops_1(A_241,k2_pre_topc(A_241,B_242))) = k2_pre_topc(A_241,B_242)
      | ~ v3_pre_topc(B_242,A_241)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1647,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1627])).

tff(c_1666,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1492,c_1430,c_1344,c_1430,c_1647])).

tff(c_1668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:55:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.67  
% 3.62/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.67  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.62/1.67  
% 3.62/1.67  %Foreground sorts:
% 3.62/1.67  
% 3.62/1.67  
% 3.62/1.67  %Background operators:
% 3.62/1.67  
% 3.62/1.67  
% 3.62/1.67  %Foreground operators:
% 3.62/1.67  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.62/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.67  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.62/1.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.62/1.67  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.62/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.62/1.67  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.62/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.62/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.67  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.62/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.62/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.62/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.62/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.62/1.67  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.62/1.67  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.62/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.62/1.67  
% 3.86/1.69  tff(f_145, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 3.86/1.69  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.86/1.69  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.86/1.69  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.86/1.69  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.86/1.69  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.86/1.69  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 3.86/1.69  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 3.86/1.69  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.86/1.69  tff(f_38, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.86/1.69  tff(f_46, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.86/1.69  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, B))) = k2_pre_topc(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tops_1)).
% 3.86/1.69  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.86/1.69  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.86/1.69  tff(c_46, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.86/1.69  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.86/1.69  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.86/1.69  tff(c_20, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.86/1.69  tff(c_286, plain, (![B_95, A_96]: (v4_pre_topc(B_95, A_96) | ~v1_xboole_0(B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.86/1.69  tff(c_308, plain, (![A_96]: (v4_pre_topc(k1_xboole_0, A_96) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(resolution, [status(thm)], [c_20, c_286])).
% 3.86/1.69  tff(c_320, plain, (![A_96]: (v4_pre_topc(k1_xboole_0, A_96) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_308])).
% 3.86/1.69  tff(c_1387, plain, (![A_217, B_218]: (k2_pre_topc(A_217, B_218)=B_218 | ~v4_pre_topc(B_218, A_217) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.86/1.69  tff(c_1436, plain, (![A_219]: (k2_pre_topc(A_219, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_219) | ~l1_pre_topc(A_219))), inference(resolution, [status(thm)], [c_20, c_1387])).
% 3.86/1.69  tff(c_1486, plain, (![A_222]: (k2_pre_topc(A_222, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222))), inference(resolution, [status(thm)], [c_320, c_1436])).
% 3.86/1.69  tff(c_1489, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1486])).
% 3.86/1.69  tff(c_1492, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1489])).
% 3.86/1.69  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.86/1.69  tff(c_304, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v1_xboole_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_286])).
% 3.86/1.69  tff(c_317, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_304])).
% 3.86/1.69  tff(c_321, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_317])).
% 3.86/1.69  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.69  tff(c_44, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.86/1.69  tff(c_174, plain, (![B_74, A_75]: (v2_tops_1(B_74, A_75) | ~v3_tops_1(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.86/1.69  tff(c_188, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_174])).
% 3.86/1.69  tff(c_200, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_188])).
% 3.86/1.69  tff(c_546, plain, (![A_130, B_131]: (k1_tops_1(A_130, B_131)=k1_xboole_0 | ~v2_tops_1(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.86/1.69  tff(c_570, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_546])).
% 3.86/1.69  tff(c_589, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_200, c_570])).
% 3.86/1.69  tff(c_976, plain, (![B_172, A_173, C_174]: (r1_tarski(B_172, k1_tops_1(A_173, C_174)) | ~r1_tarski(B_172, C_174) | ~v3_pre_topc(B_172, A_173) | ~m1_subset_1(C_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.86/1.69  tff(c_996, plain, (![B_172]: (r1_tarski(B_172, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_172, '#skF_2') | ~v3_pre_topc(B_172, '#skF_1') | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_976])).
% 3.86/1.69  tff(c_1017, plain, (![B_175]: (r1_tarski(B_175, k1_xboole_0) | ~r1_tarski(B_175, '#skF_2') | ~v3_pre_topc(B_175, '#skF_1') | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_589, c_996])).
% 3.86/1.69  tff(c_1045, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_1017])).
% 3.86/1.69  tff(c_1059, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_1045])).
% 3.86/1.69  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.86/1.69  tff(c_87, plain, (![B_53, A_54]: (~r1_xboole_0(B_53, A_54) | ~r1_tarski(B_53, A_54) | v1_xboole_0(B_53))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.86/1.69  tff(c_91, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_12, c_87])).
% 3.86/1.69  tff(c_1064, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_1059, c_91])).
% 3.86/1.69  tff(c_1073, plain, $false, inference(negUnitSimplification, [status(thm)], [c_321, c_1064])).
% 3.86/1.69  tff(c_1074, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_317])).
% 3.86/1.69  tff(c_1411, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1387])).
% 3.86/1.69  tff(c_1430, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1074, c_1411])).
% 3.86/1.69  tff(c_1301, plain, (![A_209, B_210]: (k1_tops_1(A_209, B_210)=k1_xboole_0 | ~v2_tops_1(B_210, A_209) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_pre_topc(A_209))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.86/1.69  tff(c_1325, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1301])).
% 3.86/1.69  tff(c_1344, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_200, c_1325])).
% 3.86/1.69  tff(c_1627, plain, (![A_241, B_242]: (k2_pre_topc(A_241, k1_tops_1(A_241, k2_pre_topc(A_241, B_242)))=k2_pre_topc(A_241, B_242) | ~v3_pre_topc(B_242, A_241) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.86/1.69  tff(c_1647, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1627])).
% 3.86/1.69  tff(c_1666, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1492, c_1430, c_1344, c_1430, c_1647])).
% 3.86/1.69  tff(c_1668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1666])).
% 3.86/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.69  
% 3.86/1.69  Inference rules
% 3.86/1.69  ----------------------
% 3.86/1.69  #Ref     : 0
% 3.86/1.69  #Sup     : 324
% 3.86/1.69  #Fact    : 0
% 3.86/1.69  #Define  : 0
% 3.86/1.69  #Split   : 3
% 3.86/1.69  #Chain   : 0
% 3.86/1.69  #Close   : 0
% 3.86/1.69  
% 3.86/1.69  Ordering : KBO
% 3.86/1.69  
% 3.86/1.69  Simplification rules
% 3.86/1.69  ----------------------
% 3.86/1.69  #Subsume      : 61
% 3.86/1.69  #Demod        : 224
% 3.86/1.69  #Tautology    : 91
% 3.86/1.69  #SimpNegUnit  : 5
% 3.86/1.69  #BackRed      : 0
% 3.86/1.69  
% 3.86/1.69  #Partial instantiations: 0
% 3.86/1.69  #Strategies tried      : 1
% 3.86/1.69  
% 3.86/1.69  Timing (in seconds)
% 3.86/1.69  ----------------------
% 3.86/1.69  Preprocessing        : 0.37
% 3.86/1.69  Parsing              : 0.20
% 3.86/1.69  CNF conversion       : 0.02
% 3.86/1.69  Main loop            : 0.50
% 3.86/1.69  Inferencing          : 0.19
% 3.86/1.69  Reduction            : 0.17
% 3.86/1.69  Demodulation         : 0.12
% 3.86/1.69  BG Simplification    : 0.02
% 3.86/1.69  Subsumption          : 0.08
% 3.86/1.69  Abstraction          : 0.03
% 3.86/1.69  MUC search           : 0.00
% 3.86/1.69  Cooper               : 0.00
% 3.86/1.69  Total                : 0.90
% 3.86/1.69  Index Insertion      : 0.00
% 3.86/1.69  Index Deletion       : 0.00
% 3.86/1.69  Index Matching       : 0.00
% 3.86/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
