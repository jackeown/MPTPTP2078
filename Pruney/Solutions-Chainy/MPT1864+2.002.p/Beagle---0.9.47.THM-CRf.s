%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:14 EST 2020

% Result     : Theorem 16.98s
% Output     : CNFRefutation 16.98s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 128 expanded)
%              Number of leaves         :   27 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  146 ( 388 expanded)
%              Number of equality atoms :   27 (  70 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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
    ! [B_7,A_6] :
      ( k3_xboole_0(B_7,k1_tarski(A_6)) = k1_tarski(A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [B_59,A_60] :
      ( k3_xboole_0(B_59,k1_tarski(A_60)) = k1_tarski(A_60)
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [A_60,B_59] :
      ( k3_xboole_0(k1_tarski(A_60),B_59) = k1_tarski(A_60)
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_153,plain,(
    ! [A_66,B_67,C_68] :
      ( k9_subset_1(A_66,B_67,C_68) = k3_xboole_0(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_159,plain,(
    ! [B_67] : k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4') = k3_xboole_0(B_67,'#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_153])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_553,plain,(
    ! [A_97,B_98,C_99] :
      ( v3_pre_topc('#skF_1'(A_97,B_98,C_99),A_97)
      | ~ r1_tarski(C_99,B_98)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ v2_tex_2(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5068,plain,(
    ! [A_197,B_198,B_199,C_200] :
      ( v3_pre_topc('#skF_1'(A_197,B_198,k9_subset_1(u1_struct_0(A_197),B_199,C_200)),A_197)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_197),B_199,C_200),B_198)
      | ~ v2_tex_2(B_198,A_197)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(u1_struct_0(A_197))) ) ),
    inference(resolution,[status(thm)],[c_12,c_553])).

tff(c_5086,plain,(
    ! [B_198,B_67] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_198,k3_xboole_0(B_67,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4'),B_198)
      | ~ v2_tex_2(B_198,'#skF_3')
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_5068])).

tff(c_5098,plain,(
    ! [B_198,B_67] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_198,k3_xboole_0(B_67,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_67,'#skF_4'),B_198)
      | ~ v2_tex_2(B_198,'#skF_3')
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_159,c_5086])).

tff(c_160,plain,(
    ! [B_69] : k9_subset_1(u1_struct_0('#skF_3'),B_69,'#skF_4') = k3_xboole_0(B_69,'#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_153])).

tff(c_166,plain,(
    ! [B_69] :
      ( m1_subset_1(k3_xboole_0(B_69,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_12])).

tff(c_172,plain,(
    ! [B_69] : m1_subset_1(k3_xboole_0(B_69,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_166])).

tff(c_1881,plain,(
    ! [A_126,B_127,C_128] :
      ( k9_subset_1(u1_struct_0(A_126),B_127,'#skF_1'(A_126,B_127,C_128)) = C_128
      | ~ r1_tarski(C_128,B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ v2_tex_2(B_127,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_9092,plain,(
    ! [A_229,B_230,B_231,C_232] :
      ( k9_subset_1(u1_struct_0(A_229),B_230,'#skF_1'(A_229,B_230,k9_subset_1(u1_struct_0(A_229),B_231,C_232))) = k9_subset_1(u1_struct_0(A_229),B_231,C_232)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(A_229),B_231,C_232),B_230)
      | ~ v2_tex_2(B_230,A_229)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(u1_struct_0(A_229))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1881])).

tff(c_622,plain,(
    ! [A_103,B_104,C_105] :
      ( m1_subset_1('#skF_1'(A_103,B_104,C_105),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ r1_tarski(C_105,B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ v2_tex_2(B_104,A_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [D_50] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_50) != k1_tarski('#skF_5')
      | ~ v3_pre_topc(D_50,'#skF_3')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_632,plain,(
    ! [B_104,C_105] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_104,C_105)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_104,C_105),'#skF_3')
      | ~ r1_tarski(C_105,B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_104,'#skF_3')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_622,c_28])).

tff(c_638,plain,(
    ! [B_104,C_105] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_104,C_105)) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_104,C_105),'#skF_3')
      | ~ r1_tarski(C_105,B_104)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_104,'#skF_3')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_632])).

tff(c_9104,plain,(
    ! [B_231,C_232] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_231,C_232) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k9_subset_1(u1_struct_0('#skF_3'),B_231,C_232)),'#skF_3')
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_231,C_232),'#skF_4')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'),B_231,C_232),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_231,C_232),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1(C_232,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9092,c_638])).

tff(c_17705,plain,(
    ! [B_363,C_364] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_363,C_364) != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k9_subset_1(u1_struct_0('#skF_3'),B_363,C_364)),'#skF_3')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'),B_363,C_364),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_363,C_364),'#skF_4')
      | ~ m1_subset_1(C_364,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_36,c_34,c_9104])).

tff(c_17766,plain,(
    ! [B_67] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4') != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4')),'#skF_3')
      | ~ m1_subset_1(k3_xboole_0(B_67,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),B_67,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_17705])).

tff(c_33789,plain,(
    ! [B_546] :
      ( k3_xboole_0(B_546,'#skF_4') != k1_tarski('#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4',k3_xboole_0(B_546,'#skF_4')),'#skF_3')
      | ~ r1_tarski(k3_xboole_0(B_546,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_159,c_172,c_159,c_159,c_17766])).

tff(c_33809,plain,(
    ! [B_67] :
      ( k3_xboole_0(B_67,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_67,'#skF_4'),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_5098,c_33789])).

tff(c_33870,plain,(
    ! [B_547] :
      ( k3_xboole_0(B_547,'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k3_xboole_0(B_547,'#skF_4'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_33809])).

tff(c_33922,plain,(
    ! [A_60] :
      ( k3_xboole_0(k1_tarski(A_60),'#skF_4') != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_60),'#skF_4')
      | ~ r2_hidden(A_60,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_33870])).

tff(c_34252,plain,(
    ! [A_551] :
      ( k3_xboole_0('#skF_4',k1_tarski(A_551)) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_551),'#skF_4')
      | ~ r2_hidden(A_551,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_33922])).

tff(c_34258,plain,(
    ! [A_552] :
      ( k3_xboole_0('#skF_4',k1_tarski(A_552)) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_552,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_34252])).

tff(c_34263,plain,(
    ! [A_553] :
      ( k1_tarski(A_553) != k1_tarski('#skF_5')
      | ~ r2_hidden(A_553,'#skF_4')
      | ~ r2_hidden(A_553,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_34258])).

tff(c_34265,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_34263])).

tff(c_34269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:07:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.98/8.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.98/8.86  
% 16.98/8.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.98/8.87  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 16.98/8.87  
% 16.98/8.87  %Foreground sorts:
% 16.98/8.87  
% 16.98/8.87  
% 16.98/8.87  %Background operators:
% 16.98/8.87  
% 16.98/8.87  
% 16.98/8.87  %Foreground operators:
% 16.98/8.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.98/8.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 16.98/8.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.98/8.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.98/8.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.98/8.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.98/8.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.98/8.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.98/8.87  tff('#skF_5', type, '#skF_5': $i).
% 16.98/8.87  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 16.98/8.87  tff('#skF_3', type, '#skF_3': $i).
% 16.98/8.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.98/8.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.98/8.87  tff('#skF_4', type, '#skF_4': $i).
% 16.98/8.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.98/8.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.98/8.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.98/8.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.98/8.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 16.98/8.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.98/8.87  
% 16.98/8.88  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 16.98/8.88  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 16.98/8.88  tff(f_33, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 16.98/8.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.98/8.88  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 16.98/8.88  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 16.98/8.88  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 16.98/8.88  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.98/8.88  tff(c_10, plain, (![B_7, A_6]: (k3_xboole_0(B_7, k1_tarski(A_6))=k1_tarski(A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.98/8.88  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.98/8.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.98/8.88  tff(c_92, plain, (![B_59, A_60]: (k3_xboole_0(B_59, k1_tarski(A_60))=k1_tarski(A_60) | ~r2_hidden(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.98/8.88  tff(c_98, plain, (![A_60, B_59]: (k3_xboole_0(k1_tarski(A_60), B_59)=k1_tarski(A_60) | ~r2_hidden(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 16.98/8.88  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.98/8.88  tff(c_34, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.98/8.88  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.98/8.88  tff(c_153, plain, (![A_66, B_67, C_68]: (k9_subset_1(A_66, B_67, C_68)=k3_xboole_0(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.98/8.88  tff(c_159, plain, (![B_67]: (k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4')=k3_xboole_0(B_67, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_153])).
% 16.98/8.88  tff(c_12, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.98/8.88  tff(c_553, plain, (![A_97, B_98, C_99]: (v3_pre_topc('#skF_1'(A_97, B_98, C_99), A_97) | ~r1_tarski(C_99, B_98) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_97))) | ~v2_tex_2(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_66])).
% 16.98/8.88  tff(c_5068, plain, (![A_197, B_198, B_199, C_200]: (v3_pre_topc('#skF_1'(A_197, B_198, k9_subset_1(u1_struct_0(A_197), B_199, C_200)), A_197) | ~r1_tarski(k9_subset_1(u1_struct_0(A_197), B_199, C_200), B_198) | ~v2_tex_2(B_198, A_197) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197) | ~m1_subset_1(C_200, k1_zfmisc_1(u1_struct_0(A_197))))), inference(resolution, [status(thm)], [c_12, c_553])).
% 16.98/8.88  tff(c_5086, plain, (![B_198, B_67]: (v3_pre_topc('#skF_1'('#skF_3', B_198, k3_xboole_0(B_67, '#skF_4')), '#skF_3') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4'), B_198) | ~v2_tex_2(B_198, '#skF_3') | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_159, c_5068])).
% 16.98/8.88  tff(c_5098, plain, (![B_198, B_67]: (v3_pre_topc('#skF_1'('#skF_3', B_198, k3_xboole_0(B_67, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_67, '#skF_4'), B_198) | ~v2_tex_2(B_198, '#skF_3') | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_159, c_5086])).
% 16.98/8.88  tff(c_160, plain, (![B_69]: (k9_subset_1(u1_struct_0('#skF_3'), B_69, '#skF_4')=k3_xboole_0(B_69, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_153])).
% 16.98/8.88  tff(c_166, plain, (![B_69]: (m1_subset_1(k3_xboole_0(B_69, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_160, c_12])).
% 16.98/8.88  tff(c_172, plain, (![B_69]: (m1_subset_1(k3_xboole_0(B_69, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_166])).
% 16.98/8.88  tff(c_1881, plain, (![A_126, B_127, C_128]: (k9_subset_1(u1_struct_0(A_126), B_127, '#skF_1'(A_126, B_127, C_128))=C_128 | ~r1_tarski(C_128, B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0(A_126))) | ~v2_tex_2(B_127, A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_66])).
% 16.98/8.88  tff(c_9092, plain, (![A_229, B_230, B_231, C_232]: (k9_subset_1(u1_struct_0(A_229), B_230, '#skF_1'(A_229, B_230, k9_subset_1(u1_struct_0(A_229), B_231, C_232)))=k9_subset_1(u1_struct_0(A_229), B_231, C_232) | ~r1_tarski(k9_subset_1(u1_struct_0(A_229), B_231, C_232), B_230) | ~v2_tex_2(B_230, A_229) | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229) | ~m1_subset_1(C_232, k1_zfmisc_1(u1_struct_0(A_229))))), inference(resolution, [status(thm)], [c_12, c_1881])).
% 16.98/8.88  tff(c_622, plain, (![A_103, B_104, C_105]: (m1_subset_1('#skF_1'(A_103, B_104, C_105), k1_zfmisc_1(u1_struct_0(A_103))) | ~r1_tarski(C_105, B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0(A_103))) | ~v2_tex_2(B_104, A_103) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_66])).
% 16.98/8.88  tff(c_28, plain, (![D_50]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_50)!=k1_tarski('#skF_5') | ~v3_pre_topc(D_50, '#skF_3') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.98/8.88  tff(c_632, plain, (![B_104, C_105]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_104, C_105))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_104, C_105), '#skF_3') | ~r1_tarski(C_105, B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_104, '#skF_3') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_622, c_28])).
% 16.98/8.88  tff(c_638, plain, (![B_104, C_105]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_104, C_105))!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', B_104, C_105), '#skF_3') | ~r1_tarski(C_105, B_104) | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_104, '#skF_3') | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_632])).
% 16.98/8.88  tff(c_9104, plain, (![B_231, C_232]: (k9_subset_1(u1_struct_0('#skF_3'), B_231, C_232)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k9_subset_1(u1_struct_0('#skF_3'), B_231, C_232)), '#skF_3') | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_231, C_232), '#skF_4') | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), B_231, C_232), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_231, C_232), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1(C_232, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_9092, c_638])).
% 16.98/8.88  tff(c_17705, plain, (![B_363, C_364]: (k9_subset_1(u1_struct_0('#skF_3'), B_363, C_364)!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k9_subset_1(u1_struct_0('#skF_3'), B_363, C_364)), '#skF_3') | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), B_363, C_364), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_363, C_364), '#skF_4') | ~m1_subset_1(C_364, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_36, c_34, c_9104])).
% 16.98/8.88  tff(c_17766, plain, (![B_67]: (k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4')!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4')), '#skF_3') | ~m1_subset_1(k3_xboole_0(B_67, '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), B_67, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_159, c_17705])).
% 16.98/8.88  tff(c_33789, plain, (![B_546]: (k3_xboole_0(B_546, '#skF_4')!=k1_tarski('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4', k3_xboole_0(B_546, '#skF_4')), '#skF_3') | ~r1_tarski(k3_xboole_0(B_546, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_159, c_172, c_159, c_159, c_17766])).
% 16.98/8.88  tff(c_33809, plain, (![B_67]: (k3_xboole_0(B_67, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_67, '#skF_4'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_5098, c_33789])).
% 16.98/8.88  tff(c_33870, plain, (![B_547]: (k3_xboole_0(B_547, '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k3_xboole_0(B_547, '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_33809])).
% 16.98/8.88  tff(c_33922, plain, (![A_60]: (k3_xboole_0(k1_tarski(A_60), '#skF_4')!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_60), '#skF_4') | ~r2_hidden(A_60, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_33870])).
% 16.98/8.88  tff(c_34252, plain, (![A_551]: (k3_xboole_0('#skF_4', k1_tarski(A_551))!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_551), '#skF_4') | ~r2_hidden(A_551, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_33922])).
% 16.98/8.88  tff(c_34258, plain, (![A_552]: (k3_xboole_0('#skF_4', k1_tarski(A_552))!=k1_tarski('#skF_5') | ~r2_hidden(A_552, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_34252])).
% 16.98/8.88  tff(c_34263, plain, (![A_553]: (k1_tarski(A_553)!=k1_tarski('#skF_5') | ~r2_hidden(A_553, '#skF_4') | ~r2_hidden(A_553, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_34258])).
% 16.98/8.88  tff(c_34265, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_34263])).
% 16.98/8.88  tff(c_34269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_34265])).
% 16.98/8.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.98/8.88  
% 16.98/8.88  Inference rules
% 16.98/8.88  ----------------------
% 16.98/8.88  #Ref     : 0
% 16.98/8.88  #Sup     : 8116
% 16.98/8.88  #Fact    : 0
% 16.98/8.88  #Define  : 0
% 16.98/8.88  #Split   : 2
% 16.98/8.88  #Chain   : 0
% 16.98/8.88  #Close   : 0
% 16.98/8.88  
% 16.98/8.88  Ordering : KBO
% 16.98/8.88  
% 16.98/8.88  Simplification rules
% 16.98/8.88  ----------------------
% 16.98/8.88  #Subsume      : 1489
% 16.98/8.88  #Demod        : 4568
% 16.98/8.88  #Tautology    : 1371
% 16.98/8.88  #SimpNegUnit  : 0
% 16.98/8.88  #BackRed      : 16
% 16.98/8.88  
% 16.98/8.88  #Partial instantiations: 0
% 16.98/8.88  #Strategies tried      : 1
% 16.98/8.88  
% 16.98/8.88  Timing (in seconds)
% 16.98/8.88  ----------------------
% 16.98/8.88  Preprocessing        : 0.32
% 16.98/8.88  Parsing              : 0.16
% 16.98/8.88  CNF conversion       : 0.02
% 16.98/8.88  Main loop            : 7.81
% 16.98/8.88  Inferencing          : 1.33
% 16.98/8.88  Reduction            : 4.87
% 16.98/8.89  Demodulation         : 4.57
% 16.98/8.89  BG Simplification    : 0.19
% 16.98/8.89  Subsumption          : 1.14
% 16.98/8.89  Abstraction          : 0.26
% 16.98/8.89  MUC search           : 0.00
% 16.98/8.89  Cooper               : 0.00
% 16.98/8.89  Total                : 8.16
% 16.98/8.89  Index Insertion      : 0.00
% 16.98/8.89  Index Deletion       : 0.00
% 16.98/8.89  Index Matching       : 0.00
% 16.98/8.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
