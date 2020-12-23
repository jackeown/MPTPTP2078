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
% DateTime   : Thu Dec  3 10:29:20 EST 2020

% Result     : Theorem 6.18s
% Output     : CNFRefutation 6.18s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 119 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  130 ( 357 expanded)
%              Number of equality atoms :   23 (  58 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(k1_tarski(A_4),B_5) = k1_tarski(A_4)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_52])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_78,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,C_64) = k3_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [B_67] : k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4') = k3_xboole_0(B_67,'#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k9_subset_1(A_6,B_7,C_8),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [B_67] :
      ( m1_subset_1(k3_xboole_0(B_67,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_10])).

tff(c_107,plain,(
    ! [B_67] : m1_subset_1(k3_xboole_0(B_67,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_101])).

tff(c_310,plain,(
    ! [A_95,B_96,C_97] :
      ( v4_pre_topc('#skF_1'(A_95,B_96,C_97),A_95)
      | ~ r1_tarski(C_97,B_96)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ v2_tex_2(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_320,plain,(
    ! [B_96,B_67] :
      ( v4_pre_topc('#skF_1'('#skF_3',B_96,k3_xboole_0(B_67,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_67,'#skF_4'),B_96)
      | ~ v2_tex_2(B_96,'#skF_3')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_107,c_310])).

tff(c_338,plain,(
    ! [B_96,B_67] :
      ( v4_pre_topc('#skF_1'('#skF_3',B_96,k3_xboole_0(B_67,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_67,'#skF_4'),B_96)
      | ~ v2_tex_2(B_96,'#skF_3')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_320])).

tff(c_84,plain,(
    ! [B_63] : k9_subset_1(u1_struct_0('#skF_3'),B_63,'#skF_4') = k3_xboole_0(B_63,'#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_662,plain,(
    ! [A_151,B_152,C_153] :
      ( k9_subset_1(u1_struct_0(A_151),B_152,'#skF_1'(A_151,B_152,C_153)) = C_153
      | ~ r1_tarski(C_153,B_152)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ v2_tex_2(B_152,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2914,plain,(
    ! [A_413,B_414,B_415,C_416] :
      ( k9_subset_1(u1_struct_0(A_413),B_414,'#skF_1'(A_413,B_414,k9_subset_1(u1_struct_0(A_413),B_415,C_416))) = k9_subset_1(u1_struct_0(A_413),B_415,C_416)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_413),B_415,C_416),B_414)
      | ~ v2_tex_2(B_414,A_413)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ l1_pre_topc(A_413)
      | ~ m1_subset_1(C_416,k1_zfmisc_1(u1_struct_0(A_413))) ) ),
    inference(resolution,[status(thm)],[c_10,c_662])).

tff(c_2992,plain,(
    ! [B_414,B_63] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_414,'#skF_1'('#skF_3',B_414,k3_xboole_0(B_63,'#skF_4'))) = k9_subset_1(u1_struct_0('#skF_3'),B_63,'#skF_4')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_63,'#skF_4'),B_414)
      | ~ v2_tex_2(B_414,'#skF_3')
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2914])).

tff(c_3789,plain,(
    ! [B_497,B_498] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_497,'#skF_1'('#skF_3',B_497,k3_xboole_0(B_498,'#skF_4'))) = k3_xboole_0(B_498,'#skF_4')
      | ~ r1_tarski(k3_xboole_0(B_498,'#skF_4'),B_497)
      | ~ v2_tex_2(B_497,'#skF_3')
      | ~ m1_subset_1(B_497,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_84,c_84,c_2992])).

tff(c_534,plain,(
    ! [A_130,B_131,C_132] :
      ( m1_subset_1('#skF_1'(A_130,B_131,C_132),k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ r1_tarski(C_132,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ v2_tex_2(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [D_48] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_48) != k1_tarski('#skF_5')
      | ~ v4_pre_topc(D_48,'#skF_3')
      | ~ m1_subset_1(D_48,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_548,plain,(
    ! [B_131,C_132] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_131,C_132)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_131,C_132),'#skF_3')
      | ~ r1_tarski(C_132,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_131,'#skF_3')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_534,c_26])).

tff(c_557,plain,(
    ! [B_131,C_132] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_131,C_132)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_131,C_132),'#skF_3')
      | ~ r1_tarski(C_132,B_131)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_131,'#skF_3')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_548])).

tff(c_3804,plain,(
    ! [B_498] :
      ( k3_xboole_0(B_498,'#skF_4') != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_498,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_498,'#skF_4'),'#skF_4')
      | ~ m1_subset_1(k3_xboole_0(B_498,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_498,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3789,c_557])).

tff(c_3843,plain,(
    ! [B_499] :
      ( k3_xboole_0(B_499,'#skF_4') != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_499,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_499,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_34,c_32,c_107,c_3804])).

tff(c_3847,plain,(
    ! [B_67] :
      ( k3_xboole_0(B_67,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_67,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_338,c_3843])).

tff(c_3855,plain,(
    ! [B_500] :
      ( k3_xboole_0(B_500,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_500,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3847])).

tff(c_3860,plain,(
    ! [A_501] :
      ( k3_xboole_0(k1_tarski(A_501),'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_501),'#skF_4')
      | ~ r2_hidden(A_501,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_3855])).

tff(c_3881,plain,(
    ! [A_504] :
      ( k3_xboole_0(k1_tarski(A_504),'#skF_4') != k1_tarski('#skF_5')
      | ~ r2_hidden(A_504,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_3860])).

tff(c_3886,plain,(
    ! [A_505] :
      ( k1_tarski(A_505) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_505,'#skF_4')
      | ~ r2_hidden(A_505,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_3881])).

tff(c_3888,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_3886])).

tff(c_3892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3888])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.18/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.18/2.24  
% 6.18/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.18/2.24  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 6.18/2.24  
% 6.18/2.24  %Foreground sorts:
% 6.18/2.24  
% 6.18/2.24  
% 6.18/2.24  %Background operators:
% 6.18/2.24  
% 6.18/2.24  
% 6.18/2.24  %Foreground operators:
% 6.18/2.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.18/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.18/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.18/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.18/2.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.18/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.18/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.18/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.18/2.24  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.18/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.18/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.18/2.24  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.18/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.18/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.18/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.18/2.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.18/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.18/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.18/2.24  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.18/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.18/2.24  
% 6.18/2.25  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tex_2)).
% 6.18/2.25  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.18/2.25  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.18/2.25  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.18/2.25  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 6.18/2.25  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 6.18/2.25  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.18/2.25  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.18/2.25  tff(c_52, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.18/2.25  tff(c_56, plain, (![A_4, B_5]: (k3_xboole_0(k1_tarski(A_4), B_5)=k1_tarski(A_4) | ~r2_hidden(A_4, B_5))), inference(resolution, [status(thm)], [c_8, c_52])).
% 6.18/2.25  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.18/2.25  tff(c_32, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.18/2.25  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.18/2.25  tff(c_78, plain, (![A_62, B_63, C_64]: (k9_subset_1(A_62, B_63, C_64)=k3_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.18/2.25  tff(c_95, plain, (![B_67]: (k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4')=k3_xboole_0(B_67, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_78])).
% 6.18/2.25  tff(c_10, plain, (![A_6, B_7, C_8]: (m1_subset_1(k9_subset_1(A_6, B_7, C_8), k1_zfmisc_1(A_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.18/2.25  tff(c_101, plain, (![B_67]: (m1_subset_1(k3_xboole_0(B_67, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_95, c_10])).
% 6.18/2.25  tff(c_107, plain, (![B_67]: (m1_subset_1(k3_xboole_0(B_67, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_101])).
% 6.18/2.25  tff(c_310, plain, (![A_95, B_96, C_97]: (v4_pre_topc('#skF_1'(A_95, B_96, C_97), A_95) | ~r1_tarski(C_97, B_96) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_95))) | ~v2_tex_2(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.18/2.25  tff(c_320, plain, (![B_96, B_67]: (v4_pre_topc('#skF_1'('#skF_3', B_96, k3_xboole_0(B_67, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_67, '#skF_4'), B_96) | ~v2_tex_2(B_96, '#skF_3') | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_107, c_310])).
% 6.18/2.25  tff(c_338, plain, (![B_96, B_67]: (v4_pre_topc('#skF_1'('#skF_3', B_96, k3_xboole_0(B_67, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_67, '#skF_4'), B_96) | ~v2_tex_2(B_96, '#skF_3') | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_320])).
% 6.18/2.25  tff(c_84, plain, (![B_63]: (k9_subset_1(u1_struct_0('#skF_3'), B_63, '#skF_4')=k3_xboole_0(B_63, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_78])).
% 6.18/2.25  tff(c_662, plain, (![A_151, B_152, C_153]: (k9_subset_1(u1_struct_0(A_151), B_152, '#skF_1'(A_151, B_152, C_153))=C_153 | ~r1_tarski(C_153, B_152) | ~m1_subset_1(C_153, k1_zfmisc_1(u1_struct_0(A_151))) | ~v2_tex_2(B_152, A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.18/2.25  tff(c_2914, plain, (![A_413, B_414, B_415, C_416]: (k9_subset_1(u1_struct_0(A_413), B_414, '#skF_1'(A_413, B_414, k9_subset_1(u1_struct_0(A_413), B_415, C_416)))=k9_subset_1(u1_struct_0(A_413), B_415, C_416) | ~r1_tarski(k9_subset_1(u1_struct_0(A_413), B_415, C_416), B_414) | ~v2_tex_2(B_414, A_413) | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0(A_413))) | ~l1_pre_topc(A_413) | ~m1_subset_1(C_416, k1_zfmisc_1(u1_struct_0(A_413))))), inference(resolution, [status(thm)], [c_10, c_662])).
% 6.18/2.25  tff(c_2992, plain, (![B_414, B_63]: (k9_subset_1(u1_struct_0('#skF_3'), B_414, '#skF_1'('#skF_3', B_414, k3_xboole_0(B_63, '#skF_4')))=k9_subset_1(u1_struct_0('#skF_3'), B_63, '#skF_4') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_63, '#skF_4'), B_414) | ~v2_tex_2(B_414, '#skF_3') | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_84, c_2914])).
% 6.18/2.25  tff(c_3789, plain, (![B_497, B_498]: (k9_subset_1(u1_struct_0('#skF_3'), B_497, '#skF_1'('#skF_3', B_497, k3_xboole_0(B_498, '#skF_4')))=k3_xboole_0(B_498, '#skF_4') | ~r1_tarski(k3_xboole_0(B_498, '#skF_4'), B_497) | ~v2_tex_2(B_497, '#skF_3') | ~m1_subset_1(B_497, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_84, c_84, c_2992])).
% 6.18/2.25  tff(c_534, plain, (![A_130, B_131, C_132]: (m1_subset_1('#skF_1'(A_130, B_131, C_132), k1_zfmisc_1(u1_struct_0(A_130))) | ~r1_tarski(C_132, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_130))) | ~v2_tex_2(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.18/2.25  tff(c_26, plain, (![D_48]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_48)!=k1_tarski('#skF_5') | ~v4_pre_topc(D_48, '#skF_3') | ~m1_subset_1(D_48, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.18/2.25  tff(c_548, plain, (![B_131, C_132]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_131, C_132))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_131, C_132), '#skF_3') | ~r1_tarski(C_132, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_131, '#skF_3') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_534, c_26])).
% 6.18/2.25  tff(c_557, plain, (![B_131, C_132]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_131, C_132))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_131, C_132), '#skF_3') | ~r1_tarski(C_132, B_131) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_131, '#skF_3') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_548])).
% 6.18/2.25  tff(c_3804, plain, (![B_498]: (k3_xboole_0(B_498, '#skF_4')!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_498, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_498, '#skF_4'), '#skF_4') | ~m1_subset_1(k3_xboole_0(B_498, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k3_xboole_0(B_498, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_3789, c_557])).
% 6.18/2.25  tff(c_3843, plain, (![B_499]: (k3_xboole_0(B_499, '#skF_4')!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_499, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_499, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_34, c_32, c_107, c_3804])).
% 6.18/2.25  tff(c_3847, plain, (![B_67]: (k3_xboole_0(B_67, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_67, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_338, c_3843])).
% 6.18/2.25  tff(c_3855, plain, (![B_500]: (k3_xboole_0(B_500, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_500, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3847])).
% 6.18/2.25  tff(c_3860, plain, (![A_501]: (k3_xboole_0(k1_tarski(A_501), '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_501), '#skF_4') | ~r2_hidden(A_501, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_3855])).
% 6.18/2.25  tff(c_3881, plain, (![A_504]: (k3_xboole_0(k1_tarski(A_504), '#skF_4')!=k1_tarski('#skF_5') | ~r2_hidden(A_504, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_3860])).
% 6.18/2.25  tff(c_3886, plain, (![A_505]: (k1_tarski(A_505)!=k1_tarski('#skF_5') | ~r2_hidden(A_505, '#skF_4') | ~r2_hidden(A_505, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_3881])).
% 6.18/2.25  tff(c_3888, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_3886])).
% 6.18/2.25  tff(c_3892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_3888])).
% 6.18/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.18/2.25  
% 6.18/2.25  Inference rules
% 6.18/2.25  ----------------------
% 6.18/2.25  #Ref     : 0
% 6.18/2.25  #Sup     : 961
% 6.18/2.25  #Fact    : 0
% 6.18/2.25  #Define  : 0
% 6.18/2.25  #Split   : 2
% 6.18/2.25  #Chain   : 0
% 6.18/2.25  #Close   : 0
% 6.18/2.25  
% 6.18/2.25  Ordering : KBO
% 6.18/2.25  
% 6.18/2.25  Simplification rules
% 6.18/2.26  ----------------------
% 6.18/2.26  #Subsume      : 111
% 6.18/2.26  #Demod        : 333
% 6.18/2.26  #Tautology    : 113
% 6.18/2.26  #SimpNegUnit  : 0
% 6.18/2.26  #BackRed      : 2
% 6.18/2.26  
% 6.18/2.26  #Partial instantiations: 0
% 6.18/2.26  #Strategies tried      : 1
% 6.18/2.26  
% 6.18/2.26  Timing (in seconds)
% 6.18/2.26  ----------------------
% 6.18/2.26  Preprocessing        : 0.31
% 6.18/2.26  Parsing              : 0.16
% 6.18/2.26  CNF conversion       : 0.02
% 6.18/2.26  Main loop            : 1.17
% 6.18/2.26  Inferencing          : 0.46
% 6.18/2.26  Reduction            : 0.33
% 6.18/2.26  Demodulation         : 0.23
% 6.18/2.26  BG Simplification    : 0.05
% 6.18/2.26  Subsumption          : 0.25
% 6.18/2.26  Abstraction          : 0.06
% 6.18/2.26  MUC search           : 0.00
% 6.18/2.26  Cooper               : 0.00
% 6.18/2.26  Total                : 1.50
% 6.18/2.26  Index Insertion      : 0.00
% 6.18/2.26  Index Deletion       : 0.00
% 6.18/2.26  Index Matching       : 0.00
% 6.18/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
