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
% DateTime   : Thu Dec  3 10:29:15 EST 2020

% Result     : Theorem 6.77s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 120 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  130 ( 357 expanded)
%              Number of equality atoms :   23 (  58 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_88,negated_conjecture,(
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
                         => ~ ( v3_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_66,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(k1_tarski(A_6),B_7) = k1_tarski(A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_89,plain,(
    ! [A_66,B_67,C_68] :
      ( k9_subset_1(A_66,B_67,C_68) = k3_xboole_0(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [B_69] : k9_subset_1(u1_struct_0('#skF_3'),B_69,'#skF_4') = k3_xboole_0(B_69,'#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_89])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [B_69] :
      ( m1_subset_1(k3_xboole_0(B_69,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_12])).

tff(c_108,plain,(
    ! [B_69] : m1_subset_1(k3_xboole_0(B_69,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_102])).

tff(c_394,plain,(
    ! [A_122,B_123,C_124] :
      ( v3_pre_topc('#skF_1'(A_122,B_123,C_124),A_122)
      | ~ r1_tarski(C_124,B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ v2_tex_2(B_123,A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_408,plain,(
    ! [B_123,B_69] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_123,k3_xboole_0(B_69,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_69,'#skF_4'),B_123)
      | ~ v2_tex_2(B_123,'#skF_3')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_108,c_394])).

tff(c_432,plain,(
    ! [B_123,B_69] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_123,k3_xboole_0(B_69,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_69,'#skF_4'),B_123)
      | ~ v2_tex_2(B_123,'#skF_3')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_408])).

tff(c_95,plain,(
    ! [B_67] : k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4') = k3_xboole_0(B_67,'#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_89])).

tff(c_877,plain,(
    ! [A_166,B_167,C_168] :
      ( k9_subset_1(u1_struct_0(A_166),B_167,'#skF_1'(A_166,B_167,C_168)) = C_168
      | ~ r1_tarski(C_168,B_167)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v2_tex_2(B_167,A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3215,plain,(
    ! [A_449,B_450,B_451,C_452] :
      ( k9_subset_1(u1_struct_0(A_449),B_450,'#skF_1'(A_449,B_450,k9_subset_1(u1_struct_0(A_449),B_451,C_452))) = k9_subset_1(u1_struct_0(A_449),B_451,C_452)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_449),B_451,C_452),B_450)
      | ~ v2_tex_2(B_450,A_449)
      | ~ m1_subset_1(B_450,k1_zfmisc_1(u1_struct_0(A_449)))
      | ~ l1_pre_topc(A_449)
      | ~ m1_subset_1(C_452,k1_zfmisc_1(u1_struct_0(A_449))) ) ),
    inference(resolution,[status(thm)],[c_12,c_877])).

tff(c_3303,plain,(
    ! [B_450,B_67] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_450,'#skF_1'('#skF_3',B_450,k3_xboole_0(B_67,'#skF_4'))) = k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4'),B_450)
      | ~ v2_tex_2(B_450,'#skF_3')
      | ~ m1_subset_1(B_450,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_3215])).

tff(c_3947,plain,(
    ! [B_532,B_533] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_532,'#skF_1'('#skF_3',B_532,k3_xboole_0(B_533,'#skF_4'))) = k3_xboole_0(B_533,'#skF_4')
      | ~ r1_tarski(k3_xboole_0(B_533,'#skF_4'),B_532)
      | ~ v2_tex_2(B_532,'#skF_3')
      | ~ m1_subset_1(B_532,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_95,c_95,c_3303])).

tff(c_646,plain,(
    ! [A_152,B_153,C_154] :
      ( m1_subset_1('#skF_1'(A_152,B_153,C_154),k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ r1_tarski(C_154,B_153)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ v2_tex_2(B_153,A_152)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [D_50] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_50) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_50,'#skF_3')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_662,plain,(
    ! [B_153,C_154] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_153,C_154)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_153,C_154),'#skF_3')
      | ~ r1_tarski(C_154,B_153)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_153,'#skF_3')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_646,c_28])).

tff(c_672,plain,(
    ! [B_153,C_154] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_153,C_154)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_153,C_154),'#skF_3')
      | ~ r1_tarski(C_154,B_153)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_153,'#skF_3')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_662])).

tff(c_3962,plain,(
    ! [B_533] :
      ( k3_xboole_0(B_533,'#skF_4') != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_533,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_533,'#skF_4'),'#skF_4')
      | ~ m1_subset_1(k3_xboole_0(B_533,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_533,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3947,c_672])).

tff(c_4001,plain,(
    ! [B_534] :
      ( k3_xboole_0(B_534,'#skF_4') != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_534,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_534,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_36,c_34,c_108,c_3962])).

tff(c_4005,plain,(
    ! [B_69] :
      ( k3_xboole_0(B_69,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_69,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_432,c_4001])).

tff(c_4013,plain,(
    ! [B_535] :
      ( k3_xboole_0(B_535,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_535,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_4005])).

tff(c_4018,plain,(
    ! [A_536] :
      ( k3_xboole_0(k1_tarski(A_536),'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_536),'#skF_4')
      | ~ r2_hidden(A_536,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_4013])).

tff(c_4057,plain,(
    ! [A_540] :
      ( k3_xboole_0(k1_tarski(A_540),'#skF_4') != k1_tarski('#skF_5')
      | ~ r2_hidden(A_540,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_4018])).

tff(c_4062,plain,(
    ! [A_541] :
      ( k1_tarski(A_541) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_541,'#skF_4')
      | ~ r2_hidden(A_541,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_4057])).

tff(c_4064,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_4062])).

tff(c_4068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.77/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.47  
% 6.77/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.47  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 6.77/2.47  
% 6.77/2.47  %Foreground sorts:
% 6.77/2.47  
% 6.77/2.47  
% 6.77/2.47  %Background operators:
% 6.77/2.47  
% 6.77/2.47  
% 6.77/2.47  %Foreground operators:
% 6.77/2.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.77/2.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.77/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.77/2.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.77/2.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.77/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.77/2.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.77/2.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.77/2.47  tff('#skF_5', type, '#skF_5': $i).
% 6.77/2.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.77/2.47  tff('#skF_3', type, '#skF_3': $i).
% 6.77/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.77/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.47  tff('#skF_4', type, '#skF_4': $i).
% 6.77/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.77/2.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.77/2.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.77/2.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.77/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.77/2.47  
% 7.15/2.49  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 7.15/2.49  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.15/2.49  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.15/2.49  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.15/2.49  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 7.15/2.49  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 7.15/2.49  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.15/2.49  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.15/2.49  tff(c_49, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.15/2.49  tff(c_53, plain, (![A_6, B_7]: (k3_xboole_0(k1_tarski(A_6), B_7)=k1_tarski(A_6) | ~r2_hidden(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_49])).
% 7.15/2.49  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.15/2.49  tff(c_34, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.15/2.49  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.15/2.49  tff(c_89, plain, (![A_66, B_67, C_68]: (k9_subset_1(A_66, B_67, C_68)=k3_xboole_0(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.15/2.49  tff(c_96, plain, (![B_69]: (k9_subset_1(u1_struct_0('#skF_3'), B_69, '#skF_4')=k3_xboole_0(B_69, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_89])).
% 7.15/2.49  tff(c_12, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.15/2.49  tff(c_102, plain, (![B_69]: (m1_subset_1(k3_xboole_0(B_69, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_96, c_12])).
% 7.15/2.49  tff(c_108, plain, (![B_69]: (m1_subset_1(k3_xboole_0(B_69, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_102])).
% 7.15/2.49  tff(c_394, plain, (![A_122, B_123, C_124]: (v3_pre_topc('#skF_1'(A_122, B_123, C_124), A_122) | ~r1_tarski(C_124, B_123) | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0(A_122))) | ~v2_tex_2(B_123, A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.15/2.49  tff(c_408, plain, (![B_123, B_69]: (v3_pre_topc('#skF_1'('#skF_3', B_123, k3_xboole_0(B_69, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_69, '#skF_4'), B_123) | ~v2_tex_2(B_123, '#skF_3') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_108, c_394])).
% 7.15/2.49  tff(c_432, plain, (![B_123, B_69]: (v3_pre_topc('#skF_1'('#skF_3', B_123, k3_xboole_0(B_69, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_69, '#skF_4'), B_123) | ~v2_tex_2(B_123, '#skF_3') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_408])).
% 7.15/2.49  tff(c_95, plain, (![B_67]: (k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4')=k3_xboole_0(B_67, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_89])).
% 7.15/2.49  tff(c_877, plain, (![A_166, B_167, C_168]: (k9_subset_1(u1_struct_0(A_166), B_167, '#skF_1'(A_166, B_167, C_168))=C_168 | ~r1_tarski(C_168, B_167) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(A_166))) | ~v2_tex_2(B_167, A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.15/2.49  tff(c_3215, plain, (![A_449, B_450, B_451, C_452]: (k9_subset_1(u1_struct_0(A_449), B_450, '#skF_1'(A_449, B_450, k9_subset_1(u1_struct_0(A_449), B_451, C_452)))=k9_subset_1(u1_struct_0(A_449), B_451, C_452) | ~r1_tarski(k9_subset_1(u1_struct_0(A_449), B_451, C_452), B_450) | ~v2_tex_2(B_450, A_449) | ~m1_subset_1(B_450, k1_zfmisc_1(u1_struct_0(A_449))) | ~l1_pre_topc(A_449) | ~m1_subset_1(C_452, k1_zfmisc_1(u1_struct_0(A_449))))), inference(resolution, [status(thm)], [c_12, c_877])).
% 7.15/2.49  tff(c_3303, plain, (![B_450, B_67]: (k9_subset_1(u1_struct_0('#skF_3'), B_450, '#skF_1'('#skF_3', B_450, k3_xboole_0(B_67, '#skF_4')))=k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4'), B_450) | ~v2_tex_2(B_450, '#skF_3') | ~m1_subset_1(B_450, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_95, c_3215])).
% 7.15/2.49  tff(c_3947, plain, (![B_532, B_533]: (k9_subset_1(u1_struct_0('#skF_3'), B_532, '#skF_1'('#skF_3', B_532, k3_xboole_0(B_533, '#skF_4')))=k3_xboole_0(B_533, '#skF_4') | ~r1_tarski(k3_xboole_0(B_533, '#skF_4'), B_532) | ~v2_tex_2(B_532, '#skF_3') | ~m1_subset_1(B_532, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_95, c_95, c_3303])).
% 7.15/2.49  tff(c_646, plain, (![A_152, B_153, C_154]: (m1_subset_1('#skF_1'(A_152, B_153, C_154), k1_zfmisc_1(u1_struct_0(A_152))) | ~r1_tarski(C_154, B_153) | ~m1_subset_1(C_154, k1_zfmisc_1(u1_struct_0(A_152))) | ~v2_tex_2(B_153, A_152) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.15/2.49  tff(c_28, plain, (![D_50]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_50)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_50, '#skF_3') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.15/2.49  tff(c_662, plain, (![B_153, C_154]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_153, C_154))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_153, C_154), '#skF_3') | ~r1_tarski(C_154, B_153) | ~m1_subset_1(C_154, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_153, '#skF_3') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_646, c_28])).
% 7.15/2.49  tff(c_672, plain, (![B_153, C_154]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_153, C_154))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_153, C_154), '#skF_3') | ~r1_tarski(C_154, B_153) | ~m1_subset_1(C_154, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_153, '#skF_3') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_662])).
% 7.15/2.49  tff(c_3962, plain, (![B_533]: (k3_xboole_0(B_533, '#skF_4')!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_533, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_533, '#skF_4'), '#skF_4') | ~m1_subset_1(k3_xboole_0(B_533, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k3_xboole_0(B_533, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_3947, c_672])).
% 7.15/2.49  tff(c_4001, plain, (![B_534]: (k3_xboole_0(B_534, '#skF_4')!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_534, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_534, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_36, c_34, c_108, c_3962])).
% 7.15/2.49  tff(c_4005, plain, (![B_69]: (k3_xboole_0(B_69, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_69, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_432, c_4001])).
% 7.15/2.49  tff(c_4013, plain, (![B_535]: (k3_xboole_0(B_535, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_535, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_4005])).
% 7.15/2.49  tff(c_4018, plain, (![A_536]: (k3_xboole_0(k1_tarski(A_536), '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_536), '#skF_4') | ~r2_hidden(A_536, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_4013])).
% 7.15/2.49  tff(c_4057, plain, (![A_540]: (k3_xboole_0(k1_tarski(A_540), '#skF_4')!=k1_tarski('#skF_5') | ~r2_hidden(A_540, '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_4018])).
% 7.15/2.49  tff(c_4062, plain, (![A_541]: (k1_tarski(A_541)!=k1_tarski('#skF_5') | ~r2_hidden(A_541, '#skF_4') | ~r2_hidden(A_541, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_4057])).
% 7.15/2.49  tff(c_4064, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_4062])).
% 7.15/2.49  tff(c_4068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_4064])).
% 7.15/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.49  
% 7.15/2.49  Inference rules
% 7.15/2.49  ----------------------
% 7.15/2.49  #Ref     : 0
% 7.15/2.49  #Sup     : 1005
% 7.15/2.49  #Fact    : 0
% 7.15/2.49  #Define  : 0
% 7.15/2.49  #Split   : 2
% 7.15/2.49  #Chain   : 0
% 7.15/2.49  #Close   : 0
% 7.15/2.49  
% 7.15/2.49  Ordering : KBO
% 7.15/2.49  
% 7.15/2.49  Simplification rules
% 7.15/2.49  ----------------------
% 7.15/2.49  #Subsume      : 128
% 7.15/2.49  #Demod        : 333
% 7.15/2.49  #Tautology    : 115
% 7.15/2.49  #SimpNegUnit  : 0
% 7.15/2.49  #BackRed      : 2
% 7.15/2.49  
% 7.15/2.49  #Partial instantiations: 0
% 7.15/2.49  #Strategies tried      : 1
% 7.15/2.49  
% 7.15/2.49  Timing (in seconds)
% 7.15/2.49  ----------------------
% 7.15/2.49  Preprocessing        : 0.35
% 7.15/2.49  Parsing              : 0.19
% 7.15/2.49  CNF conversion       : 0.03
% 7.15/2.49  Main loop            : 1.36
% 7.15/2.49  Inferencing          : 0.51
% 7.15/2.49  Reduction            : 0.38
% 7.15/2.49  Demodulation         : 0.27
% 7.15/2.49  BG Simplification    : 0.06
% 7.15/2.49  Subsumption          : 0.32
% 7.15/2.49  Abstraction          : 0.09
% 7.15/2.49  MUC search           : 0.00
% 7.15/2.49  Cooper               : 0.00
% 7.15/2.49  Total                : 1.74
% 7.15/2.49  Index Insertion      : 0.00
% 7.15/2.49  Index Deletion       : 0.00
% 7.15/2.49  Index Matching       : 0.00
% 7.15/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
